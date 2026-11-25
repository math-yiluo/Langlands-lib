# Determinants of standard block parabolic elements

The theorem `Langlands.GeneralLinear.determinant_blockParabolic` states, for
any commutative ring and ordered block shape, that the determinant of an
actual parabolic element is the product of the determinants of its actual
Levi projection blocks.

This is the unchanged proof that first appeared as the private
`determinant_parabolic` in `TwistedProductCharacterTwistProof` and was also copied
in `MirabolicProductMinusRightPsiGroups`. It is placed with the block-group
definitions so that both modules use one proof.

The proof reindexes the matrix by its block coordinates, applies Mathlib's
block-triangular determinant formula, and identifies each fiber with the
corresponding block. It requires no representation-theoretic hypothesis.
