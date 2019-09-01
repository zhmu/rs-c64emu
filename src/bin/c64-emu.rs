use std::process;

extern crate sdl2;
use sdl2::pixels;
use sdl2::rect::Rect;
use sdl2::pixels::Color;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;

//use sdl2::gfx::primitives::DrawRenderer;

//extern crate c64;
use ::c64::c64;

fn load_roms(memory: &mut c64::Memory) -> Result<(), c64::MemoryLoadError> {
    memory.load_rom(0xa000, "rom/basic.901226-01.bin")?;
    memory.load_rom(0xe000, "rom/kernal.901227-03.bin")?;
    memory.load_rom(0xd000, "rom/characters.901225-01.bin")?;
    Ok(())
}

fn main() {
    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem.window("rs-c64", 320, 200)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().build().unwrap();
    canvas.set_draw_color(Color::RGB(0, 255, 255));
    canvas.clear();
    canvas.present();

    let mut event_pump = sdl_context.event_pump().unwrap();

    let mut memory = c64::Memory::new();
    if let Err(err) = load_roms(&mut memory) {
        println!("cannot load roms: {:?}", err);
        process::exit(1);
    }

    let mut cpu = c64::MOS6502::new();
    if let Err(err) = cpu.reset(&mut memory) {
        println!("cpu reset error: {:?}", err);
        process::exit(1);
    }

    let mut i: u32 = 0;
    'main: loop {
        //cpu.dump();
        match cpu.execute(&mut memory) {
            Err(err) => {
                println!("cpu execute error: {:?}", err);
                process::exit(1);
            },
            _ => ()
        };

        for event in event_pump.poll_iter() {
            match event {
                Event::Quit{..} |
                Event::KeyDown{ keycode: Some(Keycode::Escape), .. } => {
                    break 'main
                },
                _ => {}
            }
        }

        i += 1;
        if i == 1000 {
            canvas.clear();
            for y in 0..25 {
                for x in 0..40 {
                    let n = memory.read_u8(0x400 + (y * 40 + x));
                    for j in 0..8 {
                        let ch = memory.read_u8(0xd000 as u16 + (n as u16 * 8) + j as u16);
                        for i in 0..8 {
                            let mut color = Color::RGB(255, 255, 255);
                            if ch & (1 << (7 - i)) != 0 {
                                color = Color::RGB(0, 0, 0);
                            }
                            let px = (x as i32 * 8 + i as i32) as i32;
                            let py = (y as i32 * 8 + j as i32) as i32;
                            canvas.set_draw_color(color);
                            canvas.fill_rect(Rect::new(px, py, 1, 1));
                            //canvas.pixel((x * 8 + i as u16) as i16, (y * 8 + j as u16) as i16, color);
                        }
                    }
                }
            }
            canvas.present();
            i = 0;
            println!("video updated");
            cpu.dump();
        }
    }
}
