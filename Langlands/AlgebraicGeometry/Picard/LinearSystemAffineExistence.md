# Every divisor of the linear system is a pullback of the universal divisor

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`. Classes are the Library's Picard group `Group` and the divisor class
`PicardHilbertPiecesReduction.dcl` (`[O(E)]`).

- `exists_affine_pullback_eq_zero`: Picard classes are trivial on small affine opens.
- `exists_point_of_affine`: over `Spec B`, a relative effective divisor `E` with
  `[O(E)] = [L_B]` is the pullback of the universal divisor along a point of `D.Gr`. The canonical
  section of `O(E)` (Library `EffectiveCartierDivisor.canonicalSection`) transported to `L_B` has
  zero locus `E` (`zeroIdeal_iso`, `zeroIdeal_canonicalSection`); it is `σ_v` for
  `v = homEquivSections⁻¹`, the values of `v` generate the unit ideal
  (`span_range_of_isRelativeEffective`), and `comap_ptMap_linePt` applies.
- `isOpenImmersion_mapX`, `range_mapX`.
- `exists_point`: for a locally noetherian `T'`, `t' : T' ⟶ Spec R` and a relative effective
  divisor `E` on `X_{T'}` with `[O(E)] = [L_{T'}] + [n']` for a class `n'` on `T'`, there is
  `k : T' ⟶ D.Gr` over `t'` with `W.comap (1 × k) = E`. The local points on affine opens where
  `n'` is trivial glue (`Scheme.Cover.glueMorphisms`), their agreement on overlaps being
  `eq_of_comap_mapX_eq`.

## Source

Kleiman, *The Picard scheme*, pp.25–26 (proof of Theorem 3.13): a divisor `D ∈ LinSys(T)` with
`O(D) ≅ L_T ⊗ f_T^*N` gives a surjection `u : Q_T → N`, hence a `T`-point of `P(Q)`.
