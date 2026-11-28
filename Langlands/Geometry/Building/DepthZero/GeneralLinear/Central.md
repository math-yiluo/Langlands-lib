# Scalar matrices and facets of KP building data of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.Central`.

## Scalar matrices (namespace `Langlands.Geometry.Building.GeneralLinearParahoric`)

- `scalarPoint u`: the scalar matrix `u · 1` (`u ∈ Fˣ`) as a rational point of `GL_N`.
- `diagGL_const_commute`, `scalarPoint_commute`, `diagonal_const_commute`: scalar matrices are
  central, over `F` and over any commutative ring.
- `innerIso_scalarPoint`: the inner automorphism of the group scheme `GL_N` given by a scalar
  matrix is the identity. On points over every test scheme the conjugating point is a scalar
  matrix (`GeneralLinear.pointsEquiv_constantPoint`), which commutes with every matrix.
- `scalarPoint_mem_fixer`: **for every building data `B` of `GL_N` over a nonarchimedean local
  field, a scalar matrix fixes every point of the reduced building.** It normalizes the maximal
  split torus through the identity of the torus, so its Weyl action is trivial
  (`weylAction_eq`); being central, it fixes every valuation of the root datum
  (`RootFunctionFamily.smul_apply`), hence every point of the apartment
  (`ValuationBuildingData.normalizer_smul_apartmentMap`); and since it commutes with `G(F)`,
  it fixes every translate `h · x` of an apartment point
  (`ValuationBuildingData.exists_smul_apartmentMap`).

This is the action-kernel fact of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*,
15.1.33 for `GL(X)`: the scalars `F^×` act trivially on the reduced building.

## Facets (namespace `Langlands.Geometry.Building.KPBuildingDatum`)

- `parahoric_eq_pointwiseFixer_inf`: for building data satisfying the one-group axioms, the
  parahoric `D.parahoric x` of a facet is the pointwise fixer of the facet intersected with
  `G(F)^0`. This is KP Axiom 4.1.20 as the Library states it
  (`BuildingModelFamily.ModelAxiomClauses.neutral_points`).
- `val_eq_singleton_of_isVertex`: under the apartment axioms, the facet containing a vertex `y`
  is `{y}`: `{y}` is a facet, and two facets sharing a point are equal
  (`ValuationBuildingData.IsFacet.eq_of_mem_mem`).
