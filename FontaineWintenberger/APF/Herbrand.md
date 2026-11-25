# The Herbrand functions ψ and φ of an APF extension

Module `FontaineWintenberger.APF.Herbrand`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K` and a separable extension `L/K`, the file defines a function `ψ` on the real line as the integral of the index `apfIndex K L`, and, when `L/K` is arithmetically profinite, its inverse `φ`.

## Definitions

- `apfHerbrandSlope K L u`: the real number `apfIndex K L (max u 0)`. It equals `1` for `u ≤ 0` (`apfHerbrandSlope_of_nonpos`).
- `apfPsi K L u`: the integral of `apfHerbrandSlope K L` from `0` to `u`. Thus `apfPsi K L u = u` for `u ≤ 0` (`apfPsi_of_nonpos`, `apfPsi_zero`), and for `u ≥ 0` it is the integral of `apfIndex K L` (`apfPsi_eq_integral_index`).
- `apfHerbrandOrderIso K L`, under `IsAPF K L`: `apfPsi K L` as an order isomorphism of `ℝ`.
- `apfPhi K L`, under `IsAPF K L`: its inverse, with `apfPsi_apfPhi` and `apfPhi_apfPsi`.

## Results

All under `IsAPF K L`:

- the slope is at least `1`, monotone and interval integrable (`IsAPF.one_le_apfHerbrandSlope`, `IsAPF.monotone_apfHerbrandSlope`, `IsAPF.intervalIntegrable_apfHerbrandSlope`);
- `apfPsi K L` is continuous, satisfies `t - s ≤ ψ(t) - ψ(s)` for `s ≤ t` (`IsAPF.apfPsi_sub_ge`), is strictly increasing, satisfies `u ≤ ψ(u)` (`IsAPF.le_apfPsi`) and is surjective;
- `apfPhi K L` is continuous and strictly increasing, and is the identity on `u ≤ 0`;
- both functions preserve the half-line `[-1, ∞)` (`IsAPF.apfPsi_mem_Ici`, `apfPhi_mem_Ici`).

Both functions depend only on the `K`-isomorphism class of `L` (`apfPsi_algEquiv`, `apfPhi_algEquiv`).

The properties of the slope come from positivity and monotonicity of the index for APF extensions; continuity of `ψ` is that of a primitive, and surjectivity follows from the intermediate value theorem.

## What to watch for

- These are the library's own functions, built from indices of subgroups of the absolute Galois group of `K`; `L/K` need not be Galois or finite. The file does not compare them with the Herbrand functions of a finite Galois extension defined from lower ramification groups.
- `apfPsi` is defined without an APF hypothesis, but its properties, and the definition of `apfPhi`, need `IsAPF K L`.
- Both functions are extended by the identity to all `u ≤ 0`, not only to `[-1, 0]`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Herbrand.lean` (SHA-256 of the source file `039283934b5d44df7fa0b446a0462c79709b87aa933d82d6c09b04776f6a6ced`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
