# Addition on the field of norms

Module `FontaineWintenberger.FieldOfNorms.Basic.Addition`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField K` and let `L/K` be a separable APF extension. The multiplicative object `FieldOfNorms K L` consists of norm-compatible families over the finite intermediate fields. The file defines its addition: the coordinate at `E` of `α + β` is the limit, over finite `F ≥ E`, of `N(α_F + β_F)`, `N` the norm from `F` to `E`. It proves that these limits exist, form a norm-compatible family, and are characterized by coordinate-wise approximation.

## Definitions

- `normSumNet K L E α β`: the net `F ↦ N(coord F α + coord F β)` indexed by the finite intermediate fields `F ≥ E`.
- `FieldOfNorms.add K L α β`: the unique element whose coordinate at every `E` is the limit of `normSumNet K L E α β`, for the spectral norm topology on `E`.

## Results

- `norm_normSumNet`, `tendsto_normSumNet_of_upper`, `norm_of_normSumNet_tendsto`, `exists_tendsto_normSumNet_of_upper_tail`, `existsUnique_fieldOfNorms_of_normSumNet_tendsto`: limits of the nets are compatible with norms, convergence above one finite field gives convergence at every finite field, and convergent nets define a unique element. These need only `K` complete and ultrametric.
- `FieldOfNorms.valuation_le_one_iff`: `FieldOfNorms.valuation K L x ≤ 1` iff every coordinate of `x` lies in the spectral integer ring.
- `IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence`: for each `s` there is a finite `T` such that for finite `T ≤ E ≤ F` and integers `x, y` of `F`, `N(x + y) − N(x) − N(y) ∈ 𝔪_E ^ s`.
- `IsAPF.exists_finiteIntermediateField_normSumNet_cauchy`, `exists_tendsto_normSumNet`: the nets are Cauchy for integral `α, β` on a tail, and converge at every `E` for all `α, β`.
- `existsUnique_fieldOfNorms_add`; then `FieldOfNorms.tendsto_normSumNet_add`, `eq_add_of_tendsto`, `add_comm`, `zero_add`, `add_zero`, `mul_add`, `valuation_add_le_one`.
- `FieldOfNorms.add_sub_mem`: for every `n`, the difference `coord E (α + β) − coord E α − coord E β` lies in `𝔪_E ^ n` for all `E` above some finite field.
- `FieldOfNorms.ext_of_eventually_sub_mem`: two elements whose coordinates agree modulo `𝔪_F ^ n` on a tail, for every `n`, are equal.

General helpers: `cauchy_map_of_eventually_sub_mem_maximalIdeal_pow` and `ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation`.

## Proofs

On the wild tail, steps are totally ramified of `p`-power degree and the relative ramification bounds grow, so an earlier estimate (`integerNorm_add_congruence_of_le_apfRamificationBound`) bounds the additive defect of the norm. Non-integral elements are handled by dividing by an element of larger valuation, using `normSumNet_mul_left`.

## Points to watch

- `add` is a binary function on the carrier, not yet an `Add` instance; associativity and negatives are not in this file.
- `add` is defined by choice from a unique-existence theorem.
- The file uses `FieldOfNorms.valuation` and its stability on a tail, from the file on the valuation.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Basic/Addition.lean` (SHA-256 of the source file `7757fbf3f3750694e70ca0f85628a6fb53d3e3a3d71721d41bae49a54289af5d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
