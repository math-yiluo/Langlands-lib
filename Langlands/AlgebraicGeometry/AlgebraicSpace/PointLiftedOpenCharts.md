# Scheme representability from point lifts into open charts

This internal construction supplies the point-coverage step in an open-chart gluing argument over an arbitrary scheme base and at every scheme universe `u`.

`HasPointLiftedOpenCharts a` says that each point `x` of a scheme chart `a : h_U → F` lifts to a point `d` of a scheme `D`, with a map `j : D → U`, and that the composite `h_D → h_U → F` factors through an open scheme chart `h_V → F` by an actual scheme map `D → V`. It requires `j(d) = x`. It imposes no etaleness, surjectivity, or residue-field-isomorphism condition on the lifting map.

`mem_residueField_of_point_lift` applies to any representable open subfunctor `A` of any presheaf `F`. If a scheme map `D → U` factors the chart through `A` and has a point over `x`, then the chart's value at the residue-field point of `x` belongs to `A`. The proof lifts `D` into the represented pullback of `A` along the chart. Its projection to `U` has `x` in its topological range. Since the residue-field-point map has image the singleton `x`, the published open-subfunctor range criterion proves the claimed membership.

`exists_representation_of_point_lifted_open_charts` assumes that `F` is an fppf sheaf and that `a` is an etale surjective scheme atlas with `HasPointLiftedOpenCharts a`. It produces an actual scheme over the original base and a natural isomorphism from that scheme's functor of points to `F`. The proof chooses one open chart and point lift for each atlas point. The preceding lemma gives residue-field membership in its open image. The published `OpenChartCoverage.isLocallySurjective_sigma_of_residueField` then proves that this family of open charts is locally surjective, and the published `openChartGluing` theorem constructs the representer. The chart family is indexed by the atlas's underlying point type, which lies in universe `u`.

The provenance is internal and derived from `OpenSubfunctorPoints`, `OpenChartCoverage`, and `OpenChartGluingProof`. The theorem assumes the open charts; it does not construct them from a locally finite type monomorphism and does not by itself prove the monomorphism schemehood statement.
