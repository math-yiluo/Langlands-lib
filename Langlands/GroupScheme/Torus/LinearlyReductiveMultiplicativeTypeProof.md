# Commutative linear reductivity and multiplicative type

Workers 538 and 787.

`Langlands.GroupScheme.commutativeLinearlyReductiveMultiplicativeType.{u}`
proves exactly the unchanged published
`Langlands.GroupScheme.CommutativeLinearlyReductiveMultiplicativeTypeStatement.{u}`.
For every field `k : Type u` and every group scheme `G` over `Spec k` with
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`IsCommMonObj G.X`, every finite matrix representation is the sum of its
simple stable subspaces if and only if `IsMultiplicativeType G`.
There are no additional hypotheses. The statement and the proof are
polymorphic in `u`.

## Implemented proof

`subsingleton_additiveHom_of_forall_semisimple` applies to an affine group scheme
over any field in universe `u`. Given semisimplicity of every matrix
representation, it applies that hypothesis to the two-dimensional representation
induced by each additive character. The additive-root obstruction gives zero at
the sole coordinate on every affine test algebra. The vector-group coordinate
extensionality helper then proves that all additive characters are equal. This
step does not use finite type or commutativity of the source.

`commutativeLinearlyReductiveMultiplicativeType` first obtains
`IsAffine G.X.left` from the affine structure morphism. For the forward
implication, it combines the preceding uniqueness result with the supplied
commutativity. These are exactly the second condition of the published
`multiplicativeTypeCharacterization`; its TFAE equivalence between conditions
two and one gives multiplicative type.

For the reverse implication, the proof takes the first conjunct of the
published `multiplicativeTypeRepresentationGaloisOrbit`, which is exactly the
required supremum of simple stable subspaces for every `n` and every
`MatrixRepresentation G (Fin n)`. Both published theorems are specialized to
`SeparableClosure k`, in the same universe as `k`.

Stability and coordinate vanishing are tested on all commutative test
algebras, including nonreduced ones. The theorem applies in every
characteristic and includes finite non-smooth groups of multiplicative type.

## Provenance and source

This module is an internal composition of four published inputs:
`MatrixRepresentation.additiveRootRepresentation_affineCoordinates_eq_zero`
from [SemisimpleAdditiveRoot](../MatrixRepresentation/SemisimpleAdditiveRoot.md),
`VectorGroup.subsingleton_hom_of_affineCoordinates_eq_zero` from
[VectorGroupAffineHomExt](../VectorGroupAffineHomExt.md),
[multiplicativeTypeCharacterization](MultiplicativeTypeCharacterizationProof.md),
and
[multiplicativeTypeRepresentationGaloisOrbit](../Rational/MultiplicativeTypeRepresentationProof.md).
Their paired Markdown files describe the underlying constructions and proofs.

The mathematical target is Milne, *Algebraic Groups* (2017), Proposition
12.54, printed p. 248, with proof on p. 249 (registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The implemented route follows its use of Theorems 12.18 and 12.30.
The additive-root helper supplies the actual composite
`G → 𝔾ₐ → SL₂ → GL₂` and derives vanishing by applying linear functionals
to its matrix coefficients on arbitrary affine tests. This all-test argument
replaces the possible universal primitive-coordinate argument described in
the statement's Markdown. Affine-point extensionality converts vanishing
into uniqueness of homomorphisms to `𝔾ₐ`, the condition used by
Theorem 12.18.
