# Galois orbit matching for a common standard family

This internal prerequisite concerns actual all-test subgroup functors and the
canonical Galois transport of a group scheme pulled back from a ground field.
It isolates the orbit argument in Springer, *Reduction theory over global
fields* (1994), §3.5, printed p.215. The proof uses the group law of the already
constructed transport; it does not use a root-height estimate.

`galoisOrbitIntersection` constructs the all-test intersection of every
canonical Galois translate of one subgroup functor. Its invariance follows
from the transport group law and bijective left multiplication of the index.
There is no assertion that this orbit intersection is always parabolic.

For a family `P` indexed by `Aut_F(L)`, suppose
`transport σ (P σ⁻¹) = P 1` for every `σ`. Applying `transport σ` to the
matching equality at `σ⁻¹` gives `transport σ (P 1) = P σ`. The transport group
law then gives `transport σ (P τ) = P (σ * τ)`. The supplied family intersection therefore equals the constructed orbit
intersection. Left multiplication is a
bijection of the index type, so the published arbitrary-intersection reindexing
theorem makes the intersection invariant. Neither finiteness nor a Galois field
extension is needed for these subgroup-functor identities.

The last theorem assumes a finite Galois extension and a central maximal split
torus in the ground-field connected reductive group. Its upper-field family
consists of canonical standard parabolic inclusions, all composed with the same
ambient group-scheme isomorphism. It retains connected reductivity upstairs,
a maximal split torus, a generic cocharacter, and every root-index subset
hypothesis. The displayed matching equality concerns the ranges of the actual
`radicalGaloisHom` inclusions on every test scheme. Rewriting it as canonical
transport matching supplies the full permutation premise of the published
finite-standard-intersection theorem. That theorem descends the actual
invariant parabolic intersection and forces every root index to be the full
simple-root set.

In Springer's argument a root and its star orbit index such a family. This
module does not construct that root action or prove that adelic overlap gives
the matching equalities. It shows that the one-member equalities suffice, so
no separate small-root assumption for each orbit member is required. It
constructs no compact set and proves no adelic compactness conclusion.
