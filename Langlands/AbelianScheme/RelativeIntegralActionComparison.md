# Relative integral restriction and ordinary pullback

This is internal comparison infrastructure for the division CM construction.
It derives its comparisons from the existing Cartier restriction and rational
extension constructions; it asserts no new result from the literature.

Let `B` be an actual abelian scheme over `S`, and let `f : T' ⟶ T` be any
morphism of schemes over `S`. The actual abelian-scheme isomorphism
`relativeBaseChangeComparisonIso` lifts the existing Cartier group-scheme
comparison. Its source is the direct pullback `B_{T'}` and its target is the
ordinary pullback along `f.left` of `B_T`. It uses the equality of structural
maps supplied by the triangle in `Over S`. No strict equality between these
two pullbacks is assumed.

`relativeEndRestrict_eq_comparison` is the literal defining formula for the
canonical relative endomorphism restriction: ordinary pullback conjugated by
this isomorphism. The intertwining equation follows by cancelling the inverse
comparison using the isomorphism equations.

For a rational algebra `A`, a full integer subalgebra `O`, and a supplied
integer basis of `O`, `integralActionRationalExtension` first rationalizes
an actual unital action on `B` and then applies the existing unique
full-order extension. It agrees with the original rationalized action on
every element of `O`. If an actual homomorphism intertwines two such integral
actions, its rationalization intertwines their extensions on every element
of `A`. The proof compares two rational-linear maps to the actual rational
Hom group on the rational basis extended from the supplied integer basis.
At each basis element it rationalizes the given actual intertwining equation.
The same full-order uniqueness proves that extension commutes with ordinary
scheme base change.

`relativeIntegralActionRationalComparisonIso` equips the rationalization of
the actual comparison isomorphism with equivariance for these actions. It
compares the extension of canonical relative restriction with the ordinary
pullback of the extended action. The resulting `classOf` equality belongs to
the existing quotient by actual equivariant rational isomorphisms. All schemes,
all morphisms over `S`, and arbitrary full integer orders with supplied bases
are allowed; no connectedness, reducedness, local noetherianness, or finite
basis assumption is added.

This module supplies a comparison, not representability or existence of
integral lifts of rational actions. It does not assert compatibility with
chosen dual data, a polarization, or adelic level data. Those conditions need
their own actual comparisons.
