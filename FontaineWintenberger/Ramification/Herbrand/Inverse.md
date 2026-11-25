# The inverse Herbrand function as an integral

Module `FontaineWintenberger.Ramification.Herbrand.Inverse`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a finite group `G` acting on a discrete valuation ring `R`, the file writes the inverse Herbrand function `ψ = inverseHerbrandFunction G` as the integral of the index `[G^0 : G^v]` of the upper ramification groups.

- `upperRamificationGroup_relIndex_eq_div`: for `u ≥ 0`, the relative index of `G^u` in `G^0` equals `|G_0| / |G^u|`.
- `intervalIntegrable_inverseHerbrand_slope`: `v ↦ |G_0| / |G^v|` is integrable on `[0, u]`.
- `exists_inverseHerbrandFunction_finite_derivative_breaks`: for a faithful action, outside a finite set of `u > 0`, `ψ` has derivative `|G_0| / |G^u|` at `u`.
- `inverseHerbrandFunction_eq_integral_div`: for a faithful action and `u ≥ 0`, `ψ(u) = ∫₀ᵘ |G_0| / |G^v| dv`.
- `inverseHerbrandFunction_eq_integral_relIndex`: the same with integrand `[G^0 : G^v]`.

The derivative of `ψ` is obtained from that of the Herbrand function by the inverse function rule; the integral formula follows by the fundamental theorem of calculus with finitely many exceptional points.

## What to watch for

The integral formulas assume `FaithfulSMul G R`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Herbrand/Inverse.lean` (SHA-256 of the source file `7e63ff6c1adf31e1c533d2b4c849e9339fb26fbae943bd0d2a98f89a7d186e71`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
