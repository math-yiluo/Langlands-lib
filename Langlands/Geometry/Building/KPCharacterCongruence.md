# Congruences tested on actual rational characters

Given a field `k`, an additive real valuation `ω`, and a group scheme `G`
over `Spec k`, `characterCongruence ω G r` is the intersection, over the
actual rational characters of `G`, of the inverse images of
`addValuationUnitFiltration ω r`. In particular every character value has
valuation zero and differs from one by an element of valuation at least `r`.

The module derives the decreasing property and the description at zero from the
corresponding scalar facts. Its intersection over all depths is precisely the
subgroup on which every rational character is one. This need not be the trivial
subgroup for a general group scheme.
For a split torus, the published
`characterLattice.pointCharacters_bijective` theorem proves that actual
characters separate points, so the intersection is trivial.

Restriction of actual characters proves that every group-scheme homomorphism
preserves these subgroups. To test membership it suffices to test any family
spanning the actual rational character module over the integers: evaluation at a
point is an additive homomorphism to the additive form of `kˣ`, and the inverse
image of the scalar congruence subgroup is an integer submodule. When the
character module is finitely generated, this gives finitely many tests.
For the openness conclusion, assume that `k` has a topology, that the underlying
scheme of `G` is affine, and that the actual rational character module is
finitely generated. If the scalar congruence subgroup is open in the induced
units topology on `kˣ`, the common character congruence subgroup is open in
exactly the canonical topology `rationalPointTopology k G.X`.

This is derived infrastructure for a torus filtration. It does not identify the
zero-depth subgroup with the torus Iwahori subgroup, supply scalar openness, or
prove centralizer or root-group properties.
