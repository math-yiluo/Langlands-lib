# The first ramification bound after a finite change of base

Module `FontaineWintenberger.APF.BaseChange.Bounds`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file shows that the bound `i(N/K) = apfRamificationBound K N` does not decrease when the base `K` is replaced by a finite extension `M` contained in `N`, in two settings: `M` a finite subextension of `SeparableClosure K` with `N` an arbitrary separable extension, and `M ≤ N` intermediate fields of a finite Galois extension `L/K`. Throughout `K` is complete discretely valued; the base change statements assume its residue field perfect.

## Definition

`apfHerbrandERealOrderIso K L`, for an APF extension `L/K`: the function `ψ = apfPsi K L` extended to an order isomorphism of the extended reals, fixing `⊤` and `⊥`. Its inverse is `apfPhi K L` on real numbers. `IsAPF.le_apfHerbrandERealOrderIso` says `u ≤ ψ(u)` for every extended real `u`.

## Results for a finite base inside the separable closure

Here `M` is a finite intermediate field of `SeparableClosure K` and `N` is a field over `M`, separable over `K`.

- `apfSubgroup_finiteBase_eq_top`: if `G_N · G_K^u = G_K` with `u ≥ -1`, then `G_N · G_M^v = G_M` for `v = apfPsi K M u`.
- `apfHerbrandERealOrderIso_bound_le`: `apfHerbrandERealOrderIso K M (i(N/K)) ≤ i(N/M)`.
- `apfRamificationBound_le_finiteBase`: `i(N/K) ≤ i(N/M)`.
- `apfStrictnessConstant_le_finiteBase`: if `N/K` is APF and `0 < i(N/K)`, then `apfStrictnessConstant K N ≤ apfStrictnessConstant M N`.

## Results inside a finite Galois extension

Here `L/K` is a finite Galois extension of normed fields and `M ≤ N` are intermediate fields; `N` over `M` is `IntermediateField.extendScalars`.

- `finiteOverfield_fixing_sup_upper_eq_top`: if `Gal(L/N) · Gal(L/K)^u = Gal(L/K)` with `u ≥ -1`, then `Gal(L/N) · Gal(L/M)^v = Gal(L/M)` for `v = apfPsi K M u`, with upper groups taken on the spectral integer ring of `L`.
- `apfHerbrandERealOrderIso_bound_le_of_finiteGalois`: `apfHerbrandERealOrderIso K M (i(N/K)) ≤ i(N/M)`.
- `apfRamificationBound_le_finiteBase_of_finiteGalois`: `i(N/K) ≤ i(N/M)`.
- `apfRamificationBound_le_step_of_finiteGalois`: for `A ≤ B ≤ N`, `i(N/K) ≤ i(B/A)`.

## Proofs

Admissible parameters are transported by the preimage formula for APF subgroups (first setting) or by the base change of upper groups in a finite Galois extension together with the modular identity for a normal subgroup (second setting). An order isomorphism commutes with suprema, and `u ≤ ψ(u)` gives the unshifted inequalities. The last result adds monotonicity of the bound along a field inclusion, proved elsewhere.

## What to watch for

- The inequalities hold in the extended reals, including the values `⊤` and `-1`.
- `apfStrictnessConstant` and `apfStrictnessRatio` are defined in another module; the comparison of strictness constants carries the hypothesis `0 < i(N/K)`.
- In the second setting the bound of `N/K` is expressed through `Gal(L/K)` by a result of another module, `apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/Bounds.lean` (SHA-256 of the source file `2cb4d6f8fb73de3addff513b40283210fe478a63c2de88e8316eb5d42205402c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
