# Inverse half-modulus block twists at one archimedean place

The product of the determinant twists used by `normalizedCuspidalBlocks`
is the inverse of the adelic Levi half-character.
`BlockShape.singleBlockInParabolic` maps a block matrix to the parabolic
by placing it in that block and setting the other Levi blocks to identity.
On this tuple the product reduces to the twist of the selected block.
The place embedding commutes with the Levi projection, so
at a real or complex place the block twist equals the reciprocal of the
restricted parabolic half-character.

On the compact block the half-character is one by
`AdelicBlockParabolicPlaceCompact`. The single-block comparison therefore
gives value one for the determinant twist on the local orthogonal or
unitary group. These identities are consequences of
`FiniteParametrizedCuspidalNormalization` and the actual local block
parabolic inclusions.
