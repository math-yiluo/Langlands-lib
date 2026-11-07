# Iterated base change of algebraic spaces

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). It contains no statement from the
literature. Base change of algebraic spaces (`baseChange g`) restricts the fppf sheaf along
`Over.map g`. Two successive base changes agree with one base change up to a canonical
isomorphism, whose effect on points is pullback along the identity of the test scheme.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.BaseChangeComparison`; morphisms
`g : T ⟶ S`, `g' : T' ⟶ T`, `g₁ : T' ⟶ S` and `h : g' ≫ g = g₁`.

- `pullback_congr_left`: pulling back sections along two morphisms over the base with the same
  underlying scheme morphism gives the same result.
- `overIso` (with `overIso_hom_left`, `overIso_inv_left`): `W` over `S` along `g₁` and along
  `g' ≫ g`, identified by the identity of `W`.
- `presheafIso`: the induced isomorphism of restricted presheaves.
- `compIso`: the isomorphism `baseChange g' (baseChange g X) ≅ baseChange g₁ X`.
- `mapSections_compIso_hom`: on sections it is pullback along `overIso`.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `continuous_ringPointsMap_of_iso`, `isHomeomorph_ringPointsMap_of_iso`: an isomorphism of
  algebraic spaces over `Spec K`, for a topological field `K`, is a homeomorphism on rational
  points for `etaleChartTopology`. Composition with the isomorphism carries étale charts to étale
  charts (`IsEtale.comp_iso`). No henselian hypothesis is needed.
- `specAlgebraMap_comp`, `towerIso`: for a tower `C → D → A`, base change along `C → D` and then
  `D → A` is base change along `C → A`.
- `baseChangeRingPointsEquiv_towerIso`: the tower isomorphism is compatible with the point
  identifications `baseChangeRingPointsEquiv`.
- `baseChangeRingPointsEquiv_changeRing`: the point identification of a base change is natural
  in the coefficient algebra.
