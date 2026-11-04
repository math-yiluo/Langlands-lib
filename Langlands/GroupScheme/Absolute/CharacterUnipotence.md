# Solvable groups with vanishing rational characters

This module derives a character criterion for unipotence and constructs the
comparison with the diagonal kernel of a chosen triangular embedding.
Everything is universe general: `k : Type u` is a field and all group schemes
are over `Spec (CommRingCat.of k)`.

## Maps to split tori

`IsSplitTorus.hom_eq_zero_of_characters_eq_zero` says that a homomorphism
`f : H ⟶ D` is zero when `D` is a split torus and every rational character
of `H` is zero. There is no smoothness, connectedness, affineness or finite
type assumption on `H` in this lemma. After choosing an isomorphism from
`D` to a finite product of copies of `Gm`, each coordinate of the composite
with `f` is a rational character. Evaluating its equality to zero on every
test scheme gives equality of all coordinates. The point equivalence for
the split torus and the all-test homomorphism extensionality theorem then
identify the map with zero.

## The diagonal kernel comparison

For `Q : TriangularTorusQuotientData H`, `Q.diagonalMap` abbreviates the
composite of the chosen closed triangular embedding with the block diagonal
map. The existing factorization through the split torus `Q.torus`, together
with the preceding lemma, proves that `Q.diagonalMap = 0` whenever all
rational characters of `H` vanish.

`Q.diagonalKernelIsoOfCharactersEqZero` is an actual group-scheme
isomorphism `H ≅ kernel Q.diagonalMap`. Its forward map is the pullback
lift of the identity of `H` and the zero map to the trivial group. Its
inverse is the original inclusion `kernelι Q.diagonalMap`. The first
inverse identity is the pullback projection identity. The second follows
by cancelling the underlying monomorphism of the kernel inclusion and
using the same projection identity. The accompanying simp lemma records
that the forward map followed by this original inclusion is the identity.

`Q.isUnipotent_of_characters_eq_zero` transports the existing unipotence
of the diagonal kernel through this isomorphism. The kernel result uses
the closed embedding into the concrete unitriangular group and the
published closed-subgroup unipotence theorem. This argument needs no
smoothness or connectedness assertion about the diagonal kernel.

## Solvable groups

`IsSolvableGroupScheme.isUnipotent_of_characters_eq_zero` concludes that
`H` is unipotent when `k` is algebraically closed, `H` is smooth, affine
and connected, `H` is solvable, and every rational character of `H` is zero.
The published Lie–Kolchin theorem supplies the chosen triangular embedding
and split torus factorization; the preceding construction finishes the
proof.

## Provenance and scope

These are internal deductions from the published rational-character,
triangular-embedding, split-torus factorization and closed-subgroup
unipotence APIs. No new external source is used. The algebraic-closedness
and solvability assumptions belong to the last corollary; the kernel
comparison itself only assumes the chosen `TriangularTorusQuotientData` and
vanishing characters. The module does not prove that a group without tori
has vanishing rational characters, does not prove maximal-torus base
change, and does not prove the arbitrary-field `NoTorusUnipotentStatement`.
