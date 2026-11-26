# Changing Gram matrices and twisting a unitary involution

Conjugation by the inverse of a change-of-basis matrix carries the
adjoint for a Gram matrix to the adjoint for its congruent Gram matrix.
Multiplying a Gram matrix by a scalar unit has the same adjoint because
the scalar commutes with every matrix.

`SecondKindInvolution.twist` takes an invertible symmetric element and
conjugates the original anti-involution by it. This preserves the
specified action on the center. The twist commutes with scalar
extension, as verified on pure tensors. For an adjoint relative to a
Gram matrix, the twist replaces that Gram matrix by its product with the
symmetric element.
