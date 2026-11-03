# Group-scheme actions specified by point laws

This internal construction removes preservation of the target group law from
the affine action bridge. `PointwiseSchemeAction` records an actual action morphism,
identity law, and associative law on every scheme test. Its target is any
scheme over the base. `AutomorphicAction.toPointwiseSchemeAction` forgets the additional
group-law preservation of an existing automorphic action.

The point action `PointwiseSchemeAction.act` is natural by composition with the action
morphism. `PointwiseSchemeAction.IsFixed` quantifies over every scheme refinement and
every acting point on it. The theorem `isFixed_iff_universal` recovers this
condition from the universal acting point on the product of the test scheme
with the acting group. For an affine acting group over `Spec R` and an affine
test, `isFixed_iff_affineRefinements` reduces fixedness to all algebra
refinements: the universal product is affine, so full faithfulness of relative
spectrum gives the needed algebra map. Cancelling the comparison isomorphism
then yields universal fixedness.

The point-law action, evaluation laws and forgetful adapter are shared with
[ImageGenerationActions](ImageGenerationActions.md), which adds equivariance
and finite-power actions. Their definitions retain the existing representation.
This point-law structure remains alongside the categorical
`SchemeAction` interface. The diagonalizable coordinate specialization is in
[AffineSchemeAction](Torus/AffineSchemeAction.md). The definitions and proofs
are internal consequences of scheme composition and the stated point laws.
