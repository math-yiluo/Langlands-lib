# Character and compact equivariance of real-place restrictions

This internal helper towards `RealPlaceFunctionalEquationStatement` is in namespace
`Langlands.Global.RankinSelbergGlobal`. It adapts the
complex-place coefficient equivariance argument to a real place, reusing the
already proved real-place point and actual compact-covariance lemmas in
`RealPlaceWhittakerCovariance`. All the conclusions of this module are proved.

Write `ι_w` for `realPlacePoint F n w`. Its mixed-coordinate entries are the
entries of the given real matrix at `w`, the identity at every other real
place, and the identity at every complex place. The module proves that its
superdiagonal sum in the infinite adeles is supported at `w`, with value the
real superdiagonal sum transported through `F_w ≅ ℝ`. Each finite adelic
superdiagonal entry is zero.

Consequently, `genericCharacter_realPlacePoint` evaluates the actual adelic
generic character at `ι_w(u)` as `realWhittakerCharacter c u`, whenever the
component of the adelic character at `w` is `realScaledCharacter c`. The
coordinate calculation uses the mixed-space ring equivalence and separate
checks at the real and complex places.

`realComponent_complex` gives this component identity for the complex-valued
character associated to a unitary additive character with
`IsRealAdditiveComponent`. `realComponent_complex_inv` gives it for the inverse
character with parameter `-a`. Its proof uses the negative argument formula
for the inverse additive character and the explicit real scaled character.

For an actual cuspidal realization `T`, a finite adelic point `b` and a vector
`x`, the restriction is `g ↦ cuspWhittaker F T χ x (ι_w(g) b)`.
`realPlaceRestriction_mul_left` proves its left upper-unipotent covariance
with character `realWhittakerCharacter c`. The proof applies the Library's
global Whittaker covariance to the genuine upper-unipotent adelic point
`ι_w(u)` and then applies the character calculation.

`realPlaceRestriction_rightTranslation` proves compact equivariance for the
coefficient map associated to any `IsRealPlaceMap A`. If `f'` is the right
translate of `f` by `k ∈ O(r+1)`, its image under `A` is the actual compact
action on `A f`. The existing compact covariance of the Whittaker integral
then translates the restriction by `k`, using multiplicativity of `ι_w`
and commutation with the finite adelic point.

These conclusions supply the character and compact clauses of
`IsRealWhittakerIntertwiner`. They assert no smoothness, growth estimate or
compatibility with Lie derivatives of the integral.
