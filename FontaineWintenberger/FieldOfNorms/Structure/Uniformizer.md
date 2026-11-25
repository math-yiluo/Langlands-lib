# A uniformizer of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Structure.Uniformizer`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`. The file produces an element of `FieldOfNorms K L` of valuation `exp(−1)` and deduces that the valuation of the field of norms is surjective and its valuation ring is a discrete valuation ring.

## Main definitions and results

- `FieldOfNorms.exists_valuation_eq_exp_neg_one`: some norm-compatible family has valuation `exp(−1)`.
- `FieldOfNorms.uniformizer`: a chosen such element, with `valuation_uniformizer`, `uniformizer_ne_zero` and `uniformizer_zpow_valuation` (the `m`-th power has valuation `exp(−m)`, for `m : ℤ`).
- `FieldOfNorms.valuation_surjective`, `fieldValuation_surjective`: the valuation is onto `WithZero (Multiplicative ℤ)`; `fieldValuation_valueGroup_eq_top` says its value group is everything.
- Instances: `FieldOfNorms.fieldValuation K L` is rank-one discrete, and its valuation subring is a discrete valuation ring. The same two instances are given for `Valued.v`, which is `fieldValuation` by definition (`FieldOfNorms.valued_v`); the file calls the second one Theorem 2.1.3 (ii).
- `FieldOfNorms.uniformizerInteger`: the uniformizer as an element of the valuation ring. It is a uniformizer for the valuation (`uniformizer_isUniformizer`), generates the maximal ideal (`uniformizer_maximalIdeal`) and is irreducible (`uniformizerInteger_irreducible`).
- `FieldOfNorms.fieldValuation_eq_normalized`: the valuation attached to the maximal ideal of the valuation ring, extended to the fraction field, equals `fieldValuation K L`.

## Proofs

Take the deep tower above the bottom field `K`. The class of a uniformizer of the first stage in the quotient by `𝔪²` lifts to a compatible family, because the transition maps are surjective (`SequentialInverseLimit.projection_surjective`). Its reconstruction `deepNormReconstruction` has a coordinate at the first stage congruent to the uniformizer modulo `𝔪²`, hence of additive valuation `1`, and the valuation of the field of norms is computed at that stage (`FieldOfNorms.valuation_eq_deepFiniteTower`). The comparison of the two valuations is checked on the uniformizer and on units, then extended to fractions.

## Points to watch

- `FieldOfNorms.uniformizer` is obtained by `choose`; only its valuation is known.
- Valuations are multiplicative: value `exp(−1)` is what the file's comments call normalized value one.
- Infinitude of `L/K` is the hypothesis `Fact (¬ Module.Finite K L)`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Uniformizer.lean` (SHA-256 of the source file `57d956ad1eff4879bb1696897f5f6c0ea45acee978a7a52c3dc1bf953534b9a2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
