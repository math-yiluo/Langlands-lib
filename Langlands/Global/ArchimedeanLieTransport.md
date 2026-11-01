# Arithmetic transport of archimedean Lie and enveloping algebras

Author: Worker 2.

This internal construction takes an actual number-field ring isomorphism
`e : K ≃+* L`, with independent field universes, and every natural matrix
rank `n`, including zero. It uses the existing arithmetic infinite-adele
transport in the mixed real and complex coordinates. It constructs maps
between the existing concrete algebras, with no supplied Lie or enveloping
transport as an input.

`realLieEquiv n e` has underlying real linear equivalence
`matrixRealLinearEquiv n e`, transported through the published identity
linear equivalences from the matrix Lie algebra to matrices. Its matrix
entry is `mixedEquiv e` applied to the original entry. The entrywise ring
equivalence preserves multiplication and subtraction, so it preserves the
matrix commutator bracket. The identity, covariant composition, and inverse
laws follow from those of the actual infinite-adele ring equivalence.

`complexLieEquiv n e` extends this real Lie equivalence by the identity on
complex coefficients. Its action on a pure tensor is
`z ⊗ X ↦ z ⊗ realLieEquiv n e X`. Mathlib's scalar-extension Lie
homomorphism proves bracket compatibility. The whole real matrix Lie
algebra is complexified, including both real directions at complex places.
The map commutes with `complexify`; tensor induction proves its identity
and composition laws, and composition gives its inverse law.

`envelopingEquiv n e` is the universal enveloping lift of that complex Lie
map into the existing actual universal enveloping algebra. It sends the
canonical generator of `X` to the canonical generator of
`complexLieEquiv n e X`. Equality on generators proves the identity and
composition laws for the lifted algebra homomorphisms. Consequently the
lift along `e.symm` is an actual two-sided inverse, giving a complex
algebra equivalence.

`centerEquiv n e` restricts the enveloping equivalence to the existing
algebra center. Surjectivity proves that images of central elements are
central; the same argument applies to the inverse. Its inclusion formula
identifies it with enveloping transport. Its identity, composition, and
inverse laws follow after inclusion. Thus all four maps have composition
law `map (e.trans a) = (map e).trans (map a)`.

Provenance is internal composition of `ArchimedeanGLTransport` and
`ArchimedeanLieAlgebra` with pinned Mathlib's matrix ring equivalence,
Lie scalar extension, universal enveloping property, and algebra-center
API. The universal lift and center restriction follow the construction
pattern of the published `ArchimedeanAdjoint`, with arithmetic transport
in place of conjugation. No new original-literature identification is
claimed. This module supplies algebraic transport; differential covariance
and preservation of finiteness conditions on functions remain separate.
