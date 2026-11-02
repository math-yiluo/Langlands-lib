# Extension from lifted generic transition units

This internal construction separates the compatibility argument from the
remaining existence of suitable lifted transition units. All schemes, rings and
index types lie in an arbitrary universe `u`.

For any scheme morphism `q : Y → X`, assume that its maps on structure-sheaf
sections over every open of `X` are injective. A family of units on the pairwise
overlaps of total opens satisfies the cocycle identity whenever its pullback
does. The proof applies the injective section map on each triple overlap and
uses naturality to commute that map with restriction and multiplication.

Suppose the total opens cover `X`, and the given actual line bundle `D` on `Y`
has frames on their inverse images. If total overlap units pull back to the
transition functions of those frames, the imported frame argument gives the
pulled-back cocycle identities and the preceding reflection gives the total
ones. `lineBundleOfTransitionLift` then constructs the actual total line bundle
using `CocycleGluing.glued` and its proved local rank-one property.
`transitionLiftIso` composes the actual pullback comparison for this glued sheaf
with the inverse frame comparison for the original `D.obj`. Its conclusion is an
isomorphism of actual module sheaves with the original sheaf.

`exists_lineBundle_of_frameCocycle_lifts` only assumes individual total-unit
lifts of all the generic frame transitions. Classical choice assembles the
lifts; reflection supplies the compatibility identity. The statement does not
assume that those lifts form a cocycle.

The same module proves that the spectrum map of any supplied fraction field
of a domain is schematically dominant. The coefficient map is injective, so
its kernel is zero, its spectrum map has dense image, and its target is
reduced. For a flat scheme over that domain, flat base change preserves this
schematic dominance. The fraction-field spectrum map is affine and thus
quasi-compact, as is its base change. The imported theorem on schematically
dominant quasi-compact morphisms proves `genericPullback_app_injective` for
every total open. No valuation, rank, Noetherianity, smoothness or properness
assumption is needed for this injectivity result.

These are derived constructions using the existing cocycle, frame and actual
pullback interfaces, together with Mathlib's dominance and flat-base-change
theorems. They have no separate literature assertion.

The existence of total-unit lifts after suitable choices of generic frames is
still a hypothesis. Local generic trivializations alone do not provide it:
a generic transition unit need not extend as a total unit. This module does
not prove global extension of all generic line bundles or the host proposition
`Langlands.AbelianScheme.ValuationRingTwoAxisExtensionStatement`.
