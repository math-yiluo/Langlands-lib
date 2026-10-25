# Compatibility of ground-base and parameter pullback

The canonical comparison `T ×_{S'} A_{S'} → T ×_S A` is natural in `T`.
Its equality on the two pullback projections gives a natural isomorphism
between the two orders of actual rigidified pullback. The isomorphism
uses the published composition coherence, so it preserves the specified
rigidification as well as the underlying line bundle.

The slice pullback adjunction identifies maps `T → P_{S'}` over `S'`
with maps `T → P` over `S`. The latter map is explicitly the former
followed by the parameter projection `P_{S'} → P`.

`baseChangeFamilyPullbackIso` combines these comparisons: pulling the
explicit `baseChangeFamily` back along a new parameter map is isomorphic
to ground-base pullback of the original family pulled back along the
corresponding old parameter map.

This is an internal construction from actual fibre products, the slice
adjunction, and rigidified pullback coherence. It imposes no restriction
on the test schemes and makes no assertion of geometric Picard-zero
preservation or representability.
