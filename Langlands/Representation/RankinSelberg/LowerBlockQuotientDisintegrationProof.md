# Lower-block quotient disintegration: proof

Authors: Worker 936 (this module, geometry and assembly) and Worker 234
(conullness of the lower triangular cell and the measure comparison helper).

This module proves the published proposition
`Langlands.RankinSelberg.LowerBlockQuotientDisintegrationStatement`
(module `Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement`)
as the theorem `Langlands.RankinSelberg.lowerBlockQuotientDisintegration`. The
statement and its Markdown are unchanged. The theorem has no hypotheses beyond
the statement's own quantifiers and premises.

## What is proved

Fix a prime `p`, a p-adic field `F` in any universe, and `n k : ℕ`. Put
`a = n + 1`, `d = k + 1` and `T = F.canonicalTopologicalData`, with the canonical
topology, valuative relation, local-field structure and Borel structures that
the statement installs. Let `chart` be the published
`lowerBlockQuotientChart : N_a \ GL_a × M_{d×a} × B̄_d → N_{a+d} \ GL_{a+d}`,
`([g], x, h) ↦ [[[g, 0], [x, h]]]`, and `D = lowerBlockQuotientDensity T a d`,
`D [g] = |det g|^(-d)`. For every additive Haar measure `η`, with
`dx = rectangularMeasure η d a`, for both right-invariance instances, and for
all compatible quotient measures `μa` on `N_a \ GL_a` and `μad` on
`N_{a+d} \ GL_{a+d}`, the theorem gives every conjunct of the statement:

1. `chart` is an open embedding;
2. `chart` is measurable;
3. `μad (range chart)ᶜ = 0`;
4. every compact open additive subgroup `K` of `M_{d×a}` has
   `0 < dx K < ∞`;
5. the measure `ρ = lowerTriangularRightHaar F T d` on `B̄_d` is regular,
   σ-finite, positive on open sets, finite on compacts and right invariant,
   and every compact open subgroup `K` of `B̄_d` has `0 < ρ K < ∞`;
6. there is a real `C > 0` with
   `μad = ENNReal.ofReal C • map chart ((μa.withDensity D).prod (dx.prod ρ))`;
7. for every Borel measurable `f : N_{a+d} \ GL_{a+d} → ℂ`, `f` is
   `μad`-integrable exactly when `f ∘ chart` is integrable for
   `(μa.withDensity D).prod (dx.prod ρ)`, and then
   `∫ f dμad = C · ∫ f (chart z) d((μa.withDensity D).prod (dx.prod ρ))(z)`.

The constant `C` is not computed. The measure identity in item 6 is an equality
of measures, not only of integrals.

## Provenance

Internal proof of an internal Library statement. The statement is motivated by
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), section 9.3, printed pp. 456-457,
where an integral over `N \ GL` is written in lower-block coordinates
`[[g, 0], [x, h]]` with measure `dg d_r(h) dx` up to a positive constant. The
source gives no proof of this change of variables. The route below (open lower
triangular cell, block coordinates, uniqueness of right-invariant measures) is
our own.

## Proof

The proof in this module only assembles results from other modules. With the
statement's local instances installed (`intro`, then the same `let`/`have`
block), it does the following.

- **Right Haar measure on `B̄_d` (item 5).** Take
  `ρ = lowerTriangularRightHaar F T (k + 1)`. Its properties are
  `lowerTriangularRightHaar_properties`, from the Library module
  `LowerBlockQuotientMeasureSupport`. Mathlib's `NeZero` instance for this
  measure gives `ρ ≠ 0`.
- **Measure identity (item 6).** Apply `lowerBlockQuotient_eq_smul_map_chart`
  (helper module `LowerBlockQuotientMeasureComparison`, Worker 234) with
  `a = n + 1`, `d = k + 1`, the given `η`, the Haar measures
  `generalLinearHaar F.Carrier n`, `unipotentHaar F.Carrier n` (for `μa`) and
  `generalLinearHaar F.Carrier (n + 1 + k)`, `unipotentHaar F.Carrier (n + 1 + k)`
  (for `μad`), the two compatibility hypotheses, and `ρ`. The regularity of
  these Haar measures comes from the published instances. Right invariance of
  the unipotent Haar measures is the statement's instance hypotheses. The
  result is `C > 0` and the identity of item 6.
- **Geometry (items 1-3).** Apply `lowerBlockQuotientGeometry p F n k μad hμad`
  (helper module `Langlands.Group.GL.LowerBlockQuotientGeometryProof`), which
  proves the published `LowerBlockQuotientGeometryStatement`.
- **Additive volumes (item 4).** `rectangularMeasure_compactOpen_pos_lt_top`
  from `LowerBlockQuotientMeasureSupport`.
- **Integrals (item 7).** `complex_integral_transfer_of_positive_scaled_map`
  from `LowerBlockQuotientMeasureSupport`, applied to the measurable chart, `C`,
  and the identity of item 6. Its integral formula needs no integrability
  hypothesis, so the conditional form required by the statement follows.

The statement's rank `n + 1 + k + 1` and the helper lemmas' rank
`(n + 1) + (k + 1)` are definitionally equal, so the helper results apply
without rewriting.

## Helper modules

These new pairs are part of this contribution. The first two are byte-identical
to the accepted helper candidates `80a38443` and `71ad0d51`, which were not yet
integrated into the Library at this contribution's base.

- `Langlands/Group/GL/LowerTriangularBlockCoordinates` (Worker 936): the block
  coordinates `B̄_a × M_{d×a} × B̄_d ≃ₜ B̄_{a+d}`,
  `(b, x, h) ↦ [[b, 0], [x, h]]`, and their group law.
- `Langlands/Group/GL/LowerTriangularBigCellConull` (Worker 234): the cosets in
  `N_m \ GL_m` with a lower triangular representative are conull for every
  compatible quotient measure.
- `Langlands/Representation/RankinSelberg/LowerTriangularQuotientCellMeasure`
  (Worker 936): uniqueness of right-invariant measures on `B̄_m` up to a
  positive constant, and the pullback of a compatible quotient measure along the
  open cell `B̄_m → N_m \ GL_m`.
- `Langlands/Group/GL/LowerBlockQuotientGeometryProof` (Worker 936): proof of
  `LowerBlockQuotientGeometryStatement` (items 1-3).
- `Langlands/Representation/RankinSelberg/LowerBlockQuotientMeasureComparison`
  (Worker 234): the measure identity of item 6 for every nonzero, σ-finite,
  right-invariant `ρ` on `B̄_d` that is finite on compacts.

The comparison also uses the published Library modules
`LowerTriangularQuotientCell` (the open cell) and
`LowerBlockWeightedProductInvariance` (Worker 113: right invariance of the
determinant-weighted product measure in block coordinates).
