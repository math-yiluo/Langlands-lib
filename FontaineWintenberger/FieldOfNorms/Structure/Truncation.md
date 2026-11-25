# The valuation ring of the field of norms as an inverse limit of truncated rings

Module `FontaineWintenberger.FieldOfNorms.Structure.Truncation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`, `D` a finite intermediate field, `𝔈 = deepFiniteTower K L D` and `𝒜 = deepNormInverseLimit K L D` the inverse limit of the quotients `𝔅 n = DeepFiniteTowerQuotient K L D n` (the integer ring of `𝔈 n` modulo `𝔪^(n+2)`) under the norm maps. The file proves that the valuation ring of `FieldOfNorms K L` is isomorphic, as a ring, to `𝒜`.

## Main definitions

- `FieldOfNorms.integralCoordinate α n`: the coordinate at `𝔈 n` of an element `α` of the valuation ring, as an element of the integer ring of `𝔈 n`.
- `FieldOfNorms.truncation n`: the ring homomorphism from the valuation ring to `𝔅 n` sending `α` to the class of its coordinate (`truncation_apply`).
- `FieldOfNorms.truncationHom`: the ring homomorphism from the valuation ring to `𝒜` with components the truncations.
- `deepIntegralReconstruction`: the map `𝒜 → valuation ring` given by `deepNormReconstruction`.
- `FieldOfNorms.truncationEquiv`: the ring isomorphism between the valuation ring and `𝒜`, with `truncationHom` in one direction and `deepIntegralReconstruction` in the other.

## Main results

- `FieldOfNorms.add_deep_sub_mem`: for integral `α`, `β`, the coordinate at `𝔈 n` of the sum `FieldOfNorms.add α β` differs from the sum of the coordinates by an element of `𝔪^(n+2)`.
- `FieldOfNorms.truncation_compatible`: the truncations are compatible with the transitions `deepFiniteTowerTransition`.
- `FieldOfNorms.truncationHom_deepIntegralReconstruction`, `deepIntegralReconstruction_truncationHom`: the two maps are inverse to each other.
- `FieldOfNorms.truncation_eq_zero_iff`: the truncation at stage `n` of `α` vanishes iff the valuation of `α` is at most `exp(−(n+2))`.

## Proofs

Addition in the field of norms is a limit of norms of sums of coordinates (`FieldOfNorms.tendsto_normSumNet_add`). The norm from any finite `F ⊇ 𝔈 n` is additive modulo `𝔪^(n+2)` (`deepFiniteTower_integerNorm_add_congruence`), and the image of `𝔪^(n+2)` is closed, so the congruence passes to the limit; this gives additivity of `truncation`. Multiplicativity is immediate, since coordinates are multiplicative. One inverse identity uses the congruence `deepNormReconstruction_sub_mem`; the other uses that the norm sequence of the coordinates of `α` is constant on its tail, together with `deepNormReconstruction_tendsto`. The kernel statement uses `FieldOfNorms.valuation_eq_deepFiniteTower`.

## Points to watch

- The coordinate maps themselves are multiplicative but not additive; only their classes modulo `𝔪^(n+2)` are ring homomorphisms.
- The inverse limit and the isomorphism depend on the chosen tower, hence on `D`.
- The valuation is multiplicative, with values in `WithZero (Multiplicative ℤ)`.
- Infinitude of `L/K` is the hypothesis `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Truncation.lean` (SHA-256 of the source file `5aa57016b8e7f6b411742c2c6d613d5f9673ca5b1e6874e5cda9d8f241404946`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
