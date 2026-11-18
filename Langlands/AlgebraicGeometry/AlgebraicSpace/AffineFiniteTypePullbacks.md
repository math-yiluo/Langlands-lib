# Finite-type affine test pullbacks

This internal helper packages represented intersections of finite-type affine test maps
into a separated algebraic space over `Spec R`, for a commutative ring `R` in an arbitrary
universe `u`. `HasFiniteTypeAffinePullbacks` requires an actual commutative `R`-algebra
`C : Type u`, finite type over `R`, and two algebra maps whose spectrum maps form the
prescribed pullback of presheaves. It imposes no étaleness hypotheses.

The proof uses the published representability of a map from a scheme to an algebraic
space. The separated diagonal makes the representing intersection a closed subscheme
of the slice product. That product is affine and locally of finite type over the base;
closed immersions preserve these properties. Its actual global-section coordinate
algebra is therefore finite type. The canonical affine isomorphism respects the given
base map, and full faithfulness of the spectrum functor converts the two projections
into the required algebra maps. Transport of the original pullback along the affine
isomorphism proves the stated presheaf pullback.

This is a derived construction from the Library's `AffineIntersections` and
`AffineSchemeTopologyFamily` results, used to apply analytification's affine-test
pullback clause. It proves no analytification or immersion conclusion by itself.
