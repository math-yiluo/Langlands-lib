# Conrad's p.17 claims on adelic points of separated algebraic spaces

Author: Worker 105.

This module assembles `Langlands.Global.AdelicSpacePointTopologyStatement`, the claims of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.17, for separated
algebraic spaces of finite type over the `S`-integers of global fields. It takes two inputs as
hypotheses:
- the filtered colimit comparison for points of algebraic spaces
  (`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointComparison`, Conrad's
  Theorem 3.4 for algebraic spaces);
- the two spread clauses (`CurvePlaceSpaceSpreadStatement`, `NumberFieldSpaceSpreadStatement`).

## Declarations

Namespace `Langlands.Global.AdelicSpacePointTopologyProof`.

- `locallyOfFinitePresentationOverBase`: over a Noetherian ring, finite type spaces are locally
  of finite presentation (`LocallyOfFinitePresentation.iff_locallyOfFiniteType`).
- `numberField_cover`, `curve_cover`: **every adelic point comes from a level**. This is the
  surjectivity half of the colimit comparison, applied to the adeles as the colimit of the levels
  (`numberFieldAdeleOverIsColimit`, `curvePlaceAdeleOverIsColimit`). The `S`-integers are
  Noetherian (`adelicSIntegersNoetherian`).
- `numberFieldSpaceAdelePoints`, `curvePlaceSpaceAdelePoints`: the Points clauses
  (`AdelicSpacePointStagesProof`, `AdelicSpacePointsProof`).
- `numberFieldSpaceAdelePointMaps`, `curvePlaceSpaceAdelePointMaps`: the Maps clauses
  (`AdelicSpacePointMapsProof`, `AdelicSpaceFibreProductProof`). The pullback square of algebraic
  spaces is a pullback square of presheaves (`CoordinateFibreProduct.isPullback_hom`).
- `adelicSpacePointTopology_of_spread`: `AdelicSpacePointTopologyStatement`, from the colimit
  comparison and the two spread clauses. The Scheme clauses are `AdelicSpacePointSchemeProof`.
