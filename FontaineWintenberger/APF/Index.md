# The inertia-relative index of an APF extension

Module `FontaineWintenberger.APF.Index`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K`, with `G_K` the Galois group of `SeparableClosure K` and `G_K^u` its absolute upper ramification groups, the file defines the natural number that measures, inside the inertia group `G_K^0`, the index of `(G_L ∩ G_K^0) · G_K^u`, and studies how it behaves in `u`, under conjugation and in a tower.

## Definitions

- `apfInertiaSubgroup K L u`, for an intermediate field `L` of `SeparableClosure K`: the subgroup `(G_L ⊓ G_K^0) ⊔ G_K^u`.
- `apfInertiaIndex K L u`: its relative index in `G_K^0`.
- `apfIndex K L u`, for an abstract separable extension `L/K`: `apfInertiaIndex` of the image of the embedding `IsSepClosed.lift`. By `apfIndex_eq_embedding` any embedding gives the same number.
- `apfTowerIndexFactor K M N u`: the relative index of `apfInertiaSubgroup K N u` in `apfInertiaSubgroup K M u`.

## Results

- `apfInertiaSubgroup_eq_inf`: for `u ≥ 0` the subgroup equals `apfSubgroup K L u ⊓ G_K^0`. It is antitone in `u` on `[0, ∞)` and lies in `G_K^0`.
- The index is `1` at `u = 0` (`apfInertiaIndex_zero`, `apfIndex_zero`). For an APF extension it is positive for `u ≥ 0` and nondecreasing on `[0, ∞)`: `IsAPF.apfIndex_pos`, `IsAPF.apfIndex_monotoneOn`, with versions for `IsAPFSubextension`.
- It is invariant under conjugation in `G_K` (`apfInertiaSubgroup_map`, `apfInertiaIndex_map`) and under `K`-isomorphism (`apfIndex_algEquiv`).
- `apfIndex_eq_index_of_apfSubgroup_zero_eq_top`: if `G_L · G_K^0 = G_K` for the image of an embedding, then `apfIndex K L u` is the index of `G_L · G_K^u` in `G_K`, for `u ≥ 0`.
- `apfSubgroup_index_eq_index_zero_mul_apfIndex`: in general the index of `G_L · G_K^u` is the index of `G_L · G_K^0` times `apfIndex K L u`.
- Towers `M ≤ N` inside the separable closure: `apfInertiaIndex_eq_mul_towerIndexFactor` and `apfIndex_eq_mul_towerIndexFactor` give index of `N` = index of `M` times `apfTowerIndexFactor K M N u` for `u ≥ 0`; `apfTowerIndexFactor_eq_inertiaRelIndex` rewrites the factor as a relative index inside `G_M ⊓ G_K^0`; it is positive and nondecreasing in `u` when `N` is APF.

The proofs are computations with relative indices of subgroups, using that `G_K^u` and `G_K^0` are normal and that conjugate embeddings give conjugate subgroups.

## What to watch for

- The index is a natural number in Mathlib's convention, so it is `0` when the relative index is infinite. Positivity is proved only for APF extensions and `u ≥ 0`; the definitions themselves need no APF hypothesis.
- The index is taken inside `G_K^0`, so the unramified part of `L/K` does not enter it; the second factorization above records the factor that is left out.
- No extension is assumed normal or finite.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Index.lean` (SHA-256 of the source file `d86d11072f120c93ed15bc5c92b82669a521fe59e685e164c46d563a29f10b04`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
