# Actual Weyl data for the GL geometric lemma

Author: Worker 14. This construction imports the published
`Langlands.Group.GL.Blocks` pair by Worker 6 and
`Langlands.Group.GL.Maps` pair by Worker 16. The complete imported pairs
were read and are reused by their current Library module names. They retain their original
authorship and are reused without modification.

`blockIndex` uses the existing consecutive-coordinate equivalence of a
positive ordered `BlockShape`. The shared identity `blockIndex_index` proves
that `blockIndex B (B.index i a) = i` by the inverse law of that equivalence;
it is used by both Bruhat descent and the minimal-representative uniqueness
proof. `blockWeyl` is the actual subgroup of
permutations of `Fin n` preserving each block. Its identity, product and
inverse closure are proved from that condition.

`IsMinimalRepresentative B C w` is the positive-root condition in type A:
`w` is strictly increasing on each individual source block, and `w^-1`
is strictly increasing on each individual target block.
`MinimalRepresentatives` is the actual finite subtype of permutations
satisfying these inequalities. No double-coset theorem is assumed by this
definition.

`weylDoubleCoset` maps this subtype to the actual quotient
`W_C \ S_n / W_B`. `parabolicDoubleCoset` maps it to the actual matrix
quotient `P_B \ GL_n / P_C` by the inverse of the existing permutation matrix.
That convention is the orbit `P_B w^-1` in BZ77. The existing permutation
homomorphism sends the standard vector `e_j` to `e_(w j)`.
Neither map is defined using a chosen bijection or an assumed Bruhat result.

`sourceParabolic`, `sourceLevi` and `sourceUnipotent` are actual subgroup
preimages under conjugation of the source Levi embedding. They describe
`M intersect w^-1(Q)`, `M intersect w^-1(N)` and `M intersect w^-1(V)`
inside the product Levi `M`. Their target analogues are obtained by
exchanging the two block shapes and replacing `w` by its inverse.

`BlockRefinement B` consists of a genuine positive ordered block shape for
each individual block of `B`. The three `refined...` constructions are
products of the actual upper parabolic, block Levi and unipotent subgroups
in those blocks. Identifying the conjugated intersections with these
standard triples is a separate theorem target, not a field of the data.

`intersectionSource` and `intersectionTarget` are ambient intersections
for any pair of group subgroups and any conjugating element.
`intersectionConjugation` constructs their multiplicative equivalence by
actual conjugation, with inverse conjugation and all intrinsic inverse and
multiplication laws proved. Its underlying value formula is also proved.
These algebraic constructions work over any commutative ring; no Bruhat
theorem over arbitrary rings is asserted.

## Source and scope

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), sections 2.1-2.2, 2.6-2.7, lemma 2.11 and geometric
lemma 2.12, printed pages 446-448 (PDF pages 7-9), and sections 6.3-6.4,
printed pages 468-469 (PDF pages 29-30).
These original passages were read. The positive-root inequalities
specialize to increasing coordinate permutations in the actual type-A
blocks. Section 6.4 specifies the inverse representative in the matrix
double-coset quotient. The source identifies both intersection triples as
standard and then uses their normalized induction and Jacquet functors.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The block-preserving subgroup and its closure proofs, subgroup preimages,
finite subtype, and conjugation equivalence are internal constructions.
Uniqueness of minimal representatives, Bruhat bijectivity, and standardness
of the intersection triples remain separate proposition definitions and
unproved obligations. No geometric-lemma or cuspidal-support proof is supplied.
