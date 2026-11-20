# Local block parabolics inside the adelic block parabolic

The real and complex group inclusions place a matrix at its chosen
archimedean place and put identity matrices elsewhere. For an ordered block
shape `B`, the same inclusions restrict to the local block parabolics.
Entries below a diagonal block vanish at the chosen place by the local
parabolic condition. The identity matrices supply zero entries at those
indices at every other place. These two facts give the global block
parabolic membership.

`leviProjection_realPlaceInclusion` and
`leviProjection_complexPlaceInclusion` show that extracting the diagonal
blocks commutes with place insertion. At the chosen place both sides
extract the same matrix entries. At each other place, the diagonal block
of the identity matrix is the identity of that block rank.

For a smooth adelic section \(f\), a local group element \(g\), and a base
point \(y\) commuting with the embedded local parabolic, the local section
has value \(f(y\iota_v(g))\).
`realPlaceSectionRestriction` and `complexPlaceSectionRestriction`
package these values in the actual space of covariant functions for the
restriction of the global normalized parabolic coefficient action.
Commutation with \(y\) transfers left covariance from the global section.
Multiplicativity of the place inclusion gives the intertwining identity for
local right translation.

The construction uses the actual group embeddings in
[`ArchimedeanPlaces`](RankinSelberg/ArchimedeanPlaces.md), the ordered
block shape and diagonal projection in
[`Blocks`](../Group/GL/Blocks.md), and the section action in
[`AdelicParabolicInduction`](AdelicParabolicInduction.md). It is the
algebraic covariance comparison for the single-place restriction.
