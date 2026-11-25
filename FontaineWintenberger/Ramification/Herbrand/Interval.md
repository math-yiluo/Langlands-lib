# Intervals under the Herbrand functions

Module `FontaineWintenberger.Ramification.Herbrand.Interval`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file contains one lemma about the Herbrand function `φ = herbrandFunction G` and its inverse `ψ = inverseHerbrandFunction G`, for a finite group `G` acting on a discrete valuation ring `R`.

`herbrandFunction_mem_Ioc_of_inverseHerbrandFunction`: let `a, b ≥ −1`. If `ψ(a) < t ≤ ψ(b)`, then `a < φ(t) ≤ b`. In other words, `φ` maps the interval `(ψ(a), ψ(b)]` into `(a, b]`.

The proof applies the strict monotonicity of `ψ` on `[−1, ∞)` and the identity `ψ(φ(t)) = t` for `t ≥ −1`, both from the basic file on the Herbrand function.

## References

Serre, *Local Fields*, Chapter IV, §3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Herbrand/Interval.lean` (SHA-256 of the source file `ce44252d15cec0cb3a5c372ba6fbf96bab8f9977ec2dc15596aae2fab6d1ca2c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
