# Semisimple tangent elements of unipotent groups vanish

This proof establishes exactly `Langlands.GroupScheme.UnipotentSemisimpleStatement`
for every universe and every field. The group is affine and locally of finite
type and is unipotent in the published representation-theoretic sense. The
semisimple predicate tests actual tangent matrices in genuine finite algebraic
group representations after extension to the algebraic closure. There are no
smoothness, connectedness, infinitude, perfection or characteristic hypotheses.
The raw tangent-kernel identity `1` represents the zero tangent vector.

The helper `UnipotentTangent` proves the dimension power bound for every tangent
matrix over every commutative test algebra by successively differentiating the
uniform ordered product identity, with a fresh square-zero parameter at each
step. The matrix is consequently nilpotent. A geometrically semisimple nilpotent
matrix becomes zero as an endomorphism over the algebraic closure by
`Module.End.eq_zero_of_isNilpotent_isSemisimple`. The matrix-to-endomorphism
coordinate equivalence and the injectivity of the field map reflect this zero
back to the original matrix. This step reuses the published
`IsGeometricallySemisimpleMatrix.eq_zero_of_isNilpotent` from
`SemisimpleNilpotentMatrix`.

The published closed linear embedding theorem supplies a faithful finite
representation of the affine finite-type group. The semisimple hypothesis and
the nilpotence result force its tangent matrix to vanish. Reconstructing the
actual dual-number point and using monicity of the closed embedding then forces
the original tangent element to equal the identity.

This is a derived implementation of the unipotent assertion in Milne,
*Algebraic Groups* (2017), Example 17.75, printed p.377 / PDF p.393. Its proof
uses the all-test product bound rather than a unitriangular embedding. It uses
the published algebraic-representation convention and asserts no comparison
with arbitrary abstract Lie-algebra representations. The Cartan generation
theorem remains a separate proof obligation.
