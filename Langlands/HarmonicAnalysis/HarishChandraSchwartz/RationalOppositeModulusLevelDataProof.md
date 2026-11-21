# Integer levels and height of the actual opposite-radical weight

The level is the negative logarithm of the discrete multiplicative valuation of the
adjoint determinant of the parabolic Iwasawa factor. Residue normalization expresses
the weight as `q^(-L/2)`. The weight is locally constant, and taking the logarithm shows
that its value determines the integer level, so the level is locally constant as well.

The root-sign criterion puts the opposite radical of any standard cocharacter in the
opposite minimal radical. Indeed a relative root pairing negatively with the standard
cocharacter cannot be positive for the generic cocharacter, by the standard chamber
condition. Genericity then makes its pairing negative for the generic cocharacter.

For `x = p k` in the opposite minimal radical, the inverse acts on the exterior
determinant vector as the inverse determinant scalar times the action of `k⁻¹`.
The vector has trivial stabilizer in the opposite radical. Its displacement
therefore bounds the closed representation's matrix norm by a power of the maximum
of one and the vector norm. Compactness bounds the contribution from `k⁻¹`.
The opposite-radical eigenvalue bound gives a uniform upper bound for the determinant
absolute value, so the same inverse determinant bounds the maximum with one.
Taking logarithms proves the lower comparison with the height.

For the upper comparison, the action of `p⁻¹` on the vector bounds the inverse
determinant absolute value by the exterior representation's matrix norm.
Power comparison between algebraic matrix norms bounds its logarithm using the
height of `p`. Since `p = x k⁻¹`, subadditivity and compactness bound this height
by the height of `x` plus a constant. The exact logarithmic identity for the
integer level gives `LevelHeightComparison`. Restriction of the locally constant
level to the opposite standard radical supplies measurability there.

This proves `RationalOppositeModulusLevelDataStatement` in the form used in
Waldspurger (2003), Lemma II.3.4 and the opening of II.4, registered as
`waldspurger-2003-plancherel`.
