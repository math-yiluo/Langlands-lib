# Coordinates of rank-one quotients on the charts of the Grassmannian

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.RingTheory.Grassmannian.LineQuotientCoordinates`. Let `Q` be an `R`-module
and `A` an `R`-algebra. A point of the Library's Grassmannian `Module.Grassmannian A (A ⊗ Q) 1`
is a submodule with locally free quotient of rank one; it lies in the chart of `x : Q`
(`Module.Grassmannian.ProjectiveEmbedding.InChart`) when the class of `1 ⊗ x` is a basis of the
quotient.

- `coord x N hN : Q →ₗ[R] A`: the coordinate of the class of `1 ⊗ m` in that basis, built from the
  Library's `Module.Grassmannian.exists_chart_equiv_linearMap`; `coord_self` (`coord x N x = 1`),
  `coord_spec`, `coord_map` (naturality in `A`), `coord_change` (coordinates in two charts differ
  by a unit).
- `linePt v hv`: for `v : Q →ₗ[R] A` whose values generate the unit ideal, the rank-one quotient
  `A ⊗ Q → A`, `a ⊗ m ↦ a v(m)`; `linePt_mkQ_eq_iff`, `linePt_inChart` (it lies in the chart of
  `x` when `v x` is a unit), `isUnit_of_inChart_linePt` (and conversely), `coord_linePt`
  (its coordinates are `(v x)⁻¹ • v`), `map_linePt` (base change), `eq_linePt_coord` (every chart
  point is the line quotient of its coordinates), `linePt_smul` (unit multiples give the same
  quotient).

## Source

These are the standard coordinates of `P(Q)` = rank-one quotients of `Q` (Kleiman, *The Picard
scheme*, p.25, proof of Theorem 3.13: a `T`-point of `P(Q)` is an invertible quotient of `Q_T`).
