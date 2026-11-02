# Signed complexes and terminal quotients for actual subgroup families

This is an internal assembly of actual subgroup function spaces, using the
published signed-complex construction. All declarations lie in
`Langlands.Aubert.SubgroupComplex`. Author: Worker 194.

Let `ι` be a finite linearly ordered set. Let `P s` and `U s` be actual
subgroups of a topological group `G`, indexed by finite subsets `s` of `ι`.
Assume only that `P s` normalizes `U s`, that `P` is antitone and that `U`
is monotone. These are structural subgroup containments. No complex,
exactness, support, classification or finite-length assertion is assumed.

`Term` is the actual smooth induced-function carrier of
`SubgroupTransition.term`. `transition` applies its canonical pointwise
quotient map to the subgroup containments. `diagram` packages these
constructed maps as the existing `CutComplex.Diagram`; its identity and
composition laws are proved from `SubgroupTransition.map_refl` and
`map_comp`. The construction does not permit arbitrary representation
maps as input.

`degreeRepresentation` is the pointwise ambient action on the finite
product of terms for `s.card = k`. The existing `CutComplex` differential
uses the sign `(-1)^(number of elements of s less than i)` on deletion of
`i`, the exterior-basis orientation for the chosen linear order.
`diagram_map_intertwining` verifies equivariance of the actual transitions,
and `differential` uses the existing general
`EquivariantDiagram.degreeDifferential_intertwining` to package the
signed map as an intertwiner. `differential_square` applies the existing
signed square-zero theorem, whose commuting-square premise was proved in
`diagram`. It is a proved construction law, not an exactness hypothesis.

`degree_isSmooth` uses the existing finite-product smoothness theorem and
smoothness of each actual induced-function space. `degreeObject` and
`degreeMorphism` bundle the smooth degree and its differential.
`degree_subsingleton` records the absence of coordinates above
`Fintype.card ι`. These statements impose no finite-length premise on `ρ`;
indeed the terms are smooth even if the original ambient action is not.

For any chosen terminal degree `k`, `boundary` is the range of the incoming
differential if `k` is positive, and the zero submodule if `k = 0`.
`boundary_stable` proves stability using differential equivariance.
`Terminal` is the actual quotient by this submodule, and
`terminalRepresentation` is its descended action. `terminalProjection`
is the canonical quotient intertwiner. Its surjectivity and exact kernel
are `terminalProjection_surjective` and `terminalProjection_ker`.
`terminalProjection_comp_differential` says that the incoming differential
is killed. Smoothness descends along this surjection
(`terminal_isSmooth`), giving `terminalObject`. None of these laws asserts
that the terminal quotient is zero.

The intended general Aubert specialization has `s` equal to the set of
removed simple roots, so that `J` is its complement. The required surviving
terminal root cardinality `|J| = |I|` is therefore cochain degree
`|S| - |I|`. This module does not assert that arbitrary subgroup families
are standard parabolics or that their complexes are exact. The realization
of that family, its canonical comparison with actual normalized
`i_J r_J`, the actual cuspidal-support category and corrected exactness
target remain separate consumers of the shared general framework.

The provenance is the constructed maps in `SubgroupTransition`, the
published generic `SignedCutComplex`, and the general `FiniteProduct` and
`EquivariantDiagram` lemmas located in `ActualCutComplex`. The latter
module also contains a separate GL specialization; no GL-specific
mathematical lemma is used here. Existing generic signs and contractions
are reused unchanged.
