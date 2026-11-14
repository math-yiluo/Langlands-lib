# The universal divisor at the points given by line quotients

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `isEmpty_of_isEffectiveCartierIdeal_bot`: the zero ideal sheaf is effective Cartier only on the
  empty scheme (its kernel module has no nonzero sections, while a frame gives `Γ(X, U)`).
- `span_range_comp`, `ptOf_pt`, `vOf_linePt`.
- `comap_ptMap_linePt`: for `v : Q → B` whose values generate the unit ideal, the universal
  divisor pulls back along the `B`-point `linePt v` to `zeroIdeal σ_v`. This is checked on the
  basic opens `D(v x)` of `Spec B`, where the point is a chart point with coordinates a unit
  multiple of `v`.
- `false_of_isRelativeEffective_of_comp_eq_zero`, `span_range_of_isRelativeEffective` (`π`
  geometrically integral): if `zeroIdeal σ_v` is relative effective Cartier, then the values of `v`
  generate the unit ideal. Otherwise `v` vanishes at the residue field of a maximal ideal; the
  pullback of the divisor to that fibre (Library `relativeEffectiveDivisorBaseChange` through
  `PicardHilbertPiecesReduction.divBC`) is `⊥`, effective Cartier, while geometric integrality
  makes the fibre nonempty.

## Source

Kleiman, *The Picard scheme*, p.25 (proof of Theorem 3.13): for `D` in `LinSys`, the fibre `D_t`
is a divisor of `X_t` by Lemma 3.4, so `σ_t ≠ 0`, `u ⊗ k_t ≠ 0` and `u` is surjective by Nakayama.
