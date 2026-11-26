# Prime-to-the-characteristic powers on unipotent points

`Langlands.GroupScheme.unipotentPowerBijective.{u}` proves
[`Langlands.GroupScheme.UnipotentPowerBijectiveStatement.{u}`](PowerBijectiveStatement.md).
For an affine unipotent group scheme `U` locally of finite type over a field `k`,
and an integer `e` whose image in `k` is nonzero, the map `x ↦ x ^ e` is a
bijection on the group of points of `U` over `AlgebraicClosure k`.

## Positive characteristic

`isPGroup_testPoints_of_isUnipotent` applies the uniform `p`-power exponent
bound to the geometric point group. The nonvanishing of `(e : k)` implies
that `p` does not divide `e.natAbs`. Mathlib's `IsPGroup.powEquiv'` gives the
bijection for the natural exponent `e.natAbs`. For a negative exponent the
integer power map is this bijection followed by inversion.

## Characteristic zero

The argument first works on rational points over a characteristic-zero
field. `smoothCommutativePointEnvelope` places each point in a commutative
closed subgroup scheme given by the schematic closure of its integer
powers. `unipotentClosedSubgroup` gives unipotence of this subgroup, so
`charZeroCommutativeUnipotentVectorGroup` makes it a vector group. In its
rational vector coordinates, the power map is multiplication by `(e : k)`
on each coordinate. Division by this scalar gives surjectivity in the
ambient point group. Injectivity on these vector groups, together with the
closed immersion into the ambient group, shows that any point with
`e`-th power one is the identity.

If two points `x` and `y` have a common `e`-th power, that power belongs to
the scheme-theoretic intersection of their closed point centralizers. The
intersection is affine, locally of finite type and unipotent, so the
surjectivity argument gives an `e`-th root `r` in it. The root `r` commutes
with both `x` and `y`. The ratios `x / r` and `y / r` then have `e`-th power
one, giving `x = r = y`.

Unipotence, affineness and local finite type pass to the base change to the
algebraic closure, and the image of `e` there is nonzero. The isomorphism
`baseChangeBasePointsEquiv` transports the rational-point bijection for
that base change to the required geometric points.

## Source

J. S. Milne, *Algebraic Groups* (Cambridge University Press, 2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Lemma 15.2 (printed p. 303) states the result. Milne's proof uses the
additive central series of Proposition 14.21 and the exactness of geometric
points in Corollary 5.48. The characteristic-zero argument here uses the
vector-group assertion of Corollary 16.15 (printed p. 329).
