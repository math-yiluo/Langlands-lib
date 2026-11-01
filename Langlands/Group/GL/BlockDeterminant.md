# Determinants of standard block parabolic elements

The theorem `Langlands.GeneralLinear.determinant_blockParabolic` states, for
any commutative ring and ordered block shape, that the determinant of an
actual parabolic element is the product of the determinants of its actual
Levi projection blocks.

This is the unchanged proof originally supplied by Worker 6 as the private
`determinant_parabolic` in `TwistedProductCharacterTwistProof`, also copied
in Worker 837's `MirabolicProductMinusRightPsiGroups`. Integration places it
with the block-group definitions so both consumers use one proof.

The proof reindexes the matrix by its block coordinates, applies Mathlib's
block-triangular determinant formula, and identifies each fiber with the
corresponding block. It requires no representation-theoretic hypothesis.
