# Exact integral witnesses for the polarized Weil-level class relation

This internal comparison refines the existing class-equality criterion in
`Langlands.Shimura.PEL.PolarizedWeilLevelClasses`. It uses the exactly
equivariant integral representatives and the exact integral polarization
cross-multiple criterion in the imported modules.

An `IntegralActionRestriction O X` is a supplied unital action of the integer
order `O` on the same actual abelian scheme as the existing polarized object
`X`. Its agreement field identifies every integral action map, after
rationalization, with the restriction of `X`'s existing rational algebra
action. The construction does not assert that such a restriction exists.

Given a finite integer basis of `O`, two supplied restrictions and an
isomorphism `e` of the existing rational actions,
`integralRestrictionIsoData` constructs actual integral maps in both
directions that exactly intertwine the order actions. They have nonzero
integer denominators, rationalize to the corresponding multiples of the
original maps of `e`, and their two composites equal the product of the
denominators times identity. The proof restricts rational equivariance to
the order and applies the existing finite torsion-clearing construction.
No fullness or lattice hypothesis is needed for this restriction argument.

`IntegralPolarizedMultiple X Y a a' q e` requires such integral data together
with an exact polarization equation. If `n` is its forward denominator,
there are integers `l` and `r`, with `l` nonzero and rational identity
`r = l * (n * n * q)`, for which the actual integral dual pullback of
`Y.polarization` along the integral forward map, multiplied by `l`, equals
`r • X.polarization`.

`multiple_iff_integralPolarizedMultiple` proves equivalence with the existing
geometric rational dual-pullback equation for the original `e` and `q`.
The forward direction supplies the exactly equivariant representatives and
then clears the polarization equation. The reverse direction uses the exact
integral equation and cancels the nonzero denominator square only in rational
Hom.

`classOf_eq_iff_integralPolarizedMultiple` retains precisely the existing
actual fixed level orbit transport, along the same `e` and with the same
`q`. It replaces the rational polarization condition by its proved equivalent
integral formulation inside the existing class-equality criterion. Proof
irrelevance identifies the reconstructed proof of the same geometric equation
with the original proof; no comparison of independently chosen isomorphisms,
multipliers, frames or orbits is used.

The integral actions and all existing geometric and level prerequisites are
inputs. No integral model existence, geometric isogeny, scheme
representability or geometric-point independence result is asserted.
