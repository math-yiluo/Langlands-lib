# Direct and successive extension of the glued affinoid atlas space

Let `K → L → M` be a tower of complete ultrametric normed fields with the
three normed algebra structures and `IsScalarTower K L M`. For any indexed
`K`-affinoid atlas `a`, take the Library's actual scalar-extended chart
quotient for `K → M`, and the quotient for `L → M` of the actual `K → L`
extended atlas. The three fields, original ambient space and chart index
have independent universes. In particular the ambient space of the
successive extension is formed from the same original chart index as the
direct extension.

`towerChartHomeomorph` compares their spectra at each original index. It is
the homeomorphism contravariantly induced by `towerEquiv` on the two actual
quotient algebras. `towerSub_iff` identifies all chart containment relations:
the intermediate extension reflects and preserves the original
containments. `towerChartHomeomorph_pull` says the component maps commute
with the restriction comaps at every containment. It applies the affinoid
naturality theorem to the original bounded restriction map, not just to its
values on points.

`towerGlued_iff` identifies the two gluing relations with the same witness
index. A common-subchart point is carried to its image under the component
homeomorphism and can be recovered by its inverse. Consequently the
component maps and inverses descend to both quotients and give
`towerHomeomorph`. Both continuities follow on the disjoint unions of chart
spectra by the quotient topology. The comparison has the indicated chart
formula in each direction (`towerHomeomorph_chart`,
`towerHomeomorph_symm_chart`), sends each direct chart domain onto the
successive one, and commutes with the projections to the original space
(`towerHomeomorph_projection`). The last equation is the projection
identity for the affinoid spectra applied on every chart. No global
Hausdorffness, nontrivial valuation or finite degree is assumed.

This is the quotient-space part of transitivity, derived from the actual
chart construction in the Library. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.4, printed p. 30 (PDF p. 27),
constructs ground field extension by gluing. Conrad–Temkin,
*Non-archimedean analytification of algebraic spaces*, 24 February 2009
preprint, Theorem 2.3.5, printed and PDF p. 13, states transitivity of the
natural analytification comparison. This module compares the analytic
spaces only as glued topological spaces with their chart homeomorphisms.
The compatible strong map with its bounded pullbacks, the localized
comparison, and the transitivity square with analytification are separate.
