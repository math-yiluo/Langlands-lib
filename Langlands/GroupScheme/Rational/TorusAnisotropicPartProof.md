# The maximal anisotropic subtorus and the almost direct product

The theorem `Langlands.GroupScheme.torusAnisotropicPart`
has exactly the published type `TorusAnisotropicPartStatement`, in every
universe `u` and over every field. The statement and its imported definitions
are preserved.

The proof first chooses a finite Galois splitting field for the actual torus.
The invariant geometric character lattice is finite free over the integers.
Descending its inclusion constructs an actual homomorphism `q : T → Q`
to a split torus, with injective geometric character pullback and image the
full invariant lattice. The anisotropic part is the full group-scheme kernel
of this map.

The kernel is closed because the split target is separated. The quotient of
the geometric character lattice by its invariants is free: the difference
map identifies this quotient with a finite torsion-free integral module.
The actual diagonalizable-kernel comparison therefore shows that the kernel
becomes a split torus over the chosen field. Integral Galois trace and the
perfect character/cocharacter pairing show that every ground-field
cocharacter of the kernel vanishes. This gives anisotropy in the published
split-rank sense.

Every homomorphism from an anisotropic torus to the split quotient is zero:
composition with each character is a rational character of the anisotropic
torus, hence zero, and characters detect homomorphisms to a split torus.
The represented kernel universal property then gives the required
factorization for every closed anisotropic subtorus.

For every largest split subtorus `a : A → T`, restriction along `a ≫ q`
is injective on character lattices. Indeed, a quotient character vanishing
on `A` has zero Galois trace by the largest-split universal property, while
invariance and torsion freeness make that character zero. Conversely,
extend a character of `A` over the splitting field and take its integral
Galois trace. This produces a character of `Q` restricting to the order
of the Galois group times the original character. Thus the pullback has
finite cokernel, and the actual split-torus character criteria show that
`A → Q` is finite and surjective. The explicit subgroup/kernel comparison
identifies `A × ker(q) → T` as its scheme pullback, giving precisely the
finite and surjective multiplication in the target.

This is an internal proof assembled from the actual torus, character descent,
kernel and largest-split constructions. Its trace arguments divide by no
integer and impose no characteristic restriction. The supporting modules
describe their implemented constructions; the original-source interpretation
of Renard V.2.2 Remark 2 and V.2.5 remains in the unchanged statement Markdown.
