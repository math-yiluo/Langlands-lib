# Realized gallery incidence and apartment connectivity

This is an internal deduction from the supplied full Tits-system comparison,
the supplied polysimplicial realization and its face compatibility. It retains
the actual valuation quotient, the original facet stabilizers, and universe
`u`; it introduces no new source assertion.

`realizationAdmissibleFacet` selects the realized facet corresponding to an
admissible parabolic, using surjectivity of the original stabilizer map.
Injectivity proves the stabilizer specification and independence of any
alternative facet with the same stabilizer. `realizationBorelFacet` specializes
this to actual conjugates of the chamber stabilizer.

A cover among admissible parabolics becomes a codimension-one face under the
reversed stabilizer order. Indeed, an intermediate realized facet would give an
intermediate admissible subgroup. The cover forces equality of stabilizers,
and injectivity forces equality of facets. For an algebraic apartment step,
the least common admissible overgroup is consequently the greatest common face
of the two realized facets, and it has codimension one in both. This supplies
the actual `IsGalleryStep`, including its meet condition.

If the two endpoints are in an actual apartment, its proved subcomplex property
puts this common face in that apartment and restricts the meet and the two
codimension statements. Normalizer Borel facets belong to the apartment whose
stabilizers form the given restricted apartment, by its empty standard type and
the injectivity of the original stabilizer map.

Assume explicitly that every singleton simple type is admissible. A simple
normalizer lift gives an algebraic step, hence an actual step between its
chosen realized Borel facets. Word induction then joins any two normalizer
Borel facets in the same actual apartment. In the empty word case the
remaining lift is in the kernel of the Weyl map, hence in the Borel, and does
not change its conjugate subgroup or its realized facet. In the induction
step, choose a lift of the first simple reflection and apply the induction
hypothesis to the remaining word. This repeats the algebraic word argument
on the actual chosen facets so that all intermediate vertices are realized
Borels; no inverse is applied to arbitrary subgroups.

The existing characterization of apartment chambers by normalizer Borel
stabilizers makes this connectivity hold for all chambers of the apartment.
Every two global chambers lie in a common actual apartment, by the full Tits
comparison. Gallery steps in that apartment are global steps: the subcomplex
property ensures that every global common subface is already in the
apartment, so the greatest-common-face and codimension conditions agree.
Thus all global chambers are connected. Together with the already proved
chamber extension and the supplied complex, this proves
`realization_isChamberComplex`.

For an apartment, `realization_isChamberComplex_apartment` combines the same
connectivity and chamber extension with an explicit `IsPolysimplicial`
premise for that apartment. The fact that the global supplied complex is
polysimplicial does not by itself discharge this apartment premise.

This module does not construct the supplied root-valuation data, full Tits
comparison or realization. Singleton admissibility, its identification with
the actual affine chamber-simple set, and the apartment polysimplicial
structure remain explicit obligations. In particular, this is a conditional
chamber-complex result, not the unconditional building construction target or
the full building axiom.
