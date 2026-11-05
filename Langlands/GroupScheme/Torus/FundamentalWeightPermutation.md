# Fundamental weights from an integral simple-coroot basis

Author: Worker 1642.

This derived lattice construction supplies another elementary step in the
fundamental-weight route to the split-torus-centralizer cocenter theorem. Its
inputs are explicit: a root datum, a root-pairing base, and integral generation
of the cocharacter lattice by all coroots. It does not derive those inputs from
the geometry of a simply connected group.

For any perfect pairing `p : M × N → R` and a finite basis `b` of `N`,
`Langlands.PermutationBasis.pairedBasis` pulls the dual basis of `N` back to `M`
through the perfect-pairing equivalence. `pairedBasis_pairing` gives the
Kronecker-delta pairing, and `pairedBasis_repr` identifies the coordinates of
`x : M` with its pairings against the right basis. Therefore the vectors
annihilating a selected subfamily of `b` form the complementary span of the left
basis. The implementation uses the previously defined `complementSpan`.

`pairedBasis_permutation` proves that pairing-preserving linear maps acting on
the two lattices permute these dual bases by the same permutation. It tests
equality against the right basis, reindexes those tests by the supplied
permutation, and applies the delta-pairing formulas. The maps need not be
packaged as group representations.

For `P : RootDatum J X Y`, `B : P.Base`, and
`hspan : P.corootSpan ℤ = ⊤`,
`Langlands.RootDatum.simpleCorootBasis` uses Mathlib's integral basis of the
root span for the flipped base. The equality `hspan` then identifies that span
with `Y`. Its values are exactly the actual simple coroots `P.coroot i`.
No hypothesis that the integral roots span `X` is required.

`fundamentalWeightBasis` dualizes this simple-coroot basis through the root
datum's perfect integral pairing. Its pairing and coordinate lemmas prove
that these are the fundamental weights. The complement lemma characterizes
the characters vanishing on a chosen set of simple coroots, and the permutation
lemma transfers any pairing-preserving permutation of simple coroots to their
fundamental weights.

These results follow directly from Mathlib's `RootPairing.Base.toWeightBasisInt`,
`Module.Basis.dualBasis`, and perfect-pairing APIs. Their provenance is internal
linear algebra motivated by the route in the public
`SplitTorusCentralizerCocenterStatement` Markdown. The geometric existence of a
base, the integral coroot-span equality, the identification of a cocenter
character image, and the Weyl and Galois action comparisons remain obligations.
