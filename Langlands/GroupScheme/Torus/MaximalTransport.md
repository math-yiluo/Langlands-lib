# Transport of maximal tori through isomorphisms and closed subgroups

Worker 1336.

This module supplies elementary consequences of the published `IsTorus`,
`IsMaximalTorus`, `IsClosedSubgroup`, and `SubgroupConjugate` definitions.
It also defines the individual-group property `MaximalToriAreConjugate`.
The construction and proofs are derived internal infrastructure; they do
not invoke a structural conjugacy or existence theorem from the literature.

The field is arbitrary, and all group schemes, isomorphisms, and
factorizations are over that field, at universe `u`.

`IsTorus.of_iso` and `IsTorus.iso_iff` preserve the chosen splitting
extension and transport the split-torus isomorphism after applying the
base-change functor.

`IsMaximalTorus.comp_iso` and `comp_iso_iff` transport maximality through an
ambient group isomorphism. A proposed larger torus in the new ambient
group is composed with the inverse ambient isomorphism, so the original
maximality condition makes its factor map an isomorphism.
`IsMaximalTorus.iso_comp` and `iso_comp_iff` handle an isomorphism of the
source group schemes. The factor map is composed with the inverse source
isomorphism, the original maximality condition is applied, and the source
isomorphism is composed back.

`IsMaximalTorus.of_comp` states that if `f ≫ j` is an ambient maximal
torus and `j` is a closed subgroup, then `f` is a maximal torus of the
intermediate group. Closedness of `f` follows from the published
`IsClosedSubgroup.of_comp`. Any larger torus in the intermediate group
gives a larger closed torus in the ambient group by composition with `j`.

`SubgroupConjugate.isMaximalTorus_iff` combines source and ambient
isomorphism transport with the conjugacy equation. It allows different
commutative source groups; the isomorphism in `SubgroupConjugate` is an
isomorphism of their underlying group schemes.

`MaximalToriAreConjugate G` says that every pair of maximal tori of `G`
is related by `SubgroupConjugate`, with a point over the base field and an
isomorphism of source group schemes. This is a property, with no assertion
that it holds for arbitrary `G`. Its `of_iso` theorem transports that
property through an ambient group isomorphism.

The final theorem, `MaximalToriAreConjugate.isMaximalTorus_comp`, isolates
the conjugacy step needed in proofs about maximal tori in parabolics.
Suppose `j : H ⟶ G` is closed, the maximal tori of `H` are conjugate,
and one maximal torus of `G` factors through `H`. Then every maximal torus
of `H` is maximal in `G`. The proof first restricts the known ambient
maximal torus to `H`, conjugates the two tori in `H`, maps that conjugacy
to `G`, and applies invariance of maximality under conjugacy.

This module proves no general maximal-torus existence, conjugacy,
preservation under field extension, or parabolic-containment theorem.
Those structural results remain separate obligations for the exact
`ParabolicMaximalTorusStatement`.
