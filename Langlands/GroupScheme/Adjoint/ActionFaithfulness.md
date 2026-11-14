# Faithfulness of full-centre quotient actions

This is a derived helper for the arbitrary-base connected-action innerness
proof. It generalizes the field argument in
`IsAdjointQuotient.innerAction_kernel` and `innerAction_isFaithful` from
`Langlands.GroupScheme.Rational.InnerDiscrepancy`. It assumes a supplied
`RelativeRoot.IsFppfQuotient (center G) q` and a supplied action whose restriction
along `q` is conjugation. It does not assert the existence of this quotient or
action.

`hom_ext_of_flat_surjective_local_lift` checks equality of maps after locally
lifting a quotient point. The proof forms the scheme pullback of that point
along the quotient map. Its projection to the test scheme is flat and
surjective, hence an epimorphism. Cancelling this projection proves equality.
Only flatness and surjectivity of the quotient map are used. This is the same
pullback argument as `AutomorphicAction.hom_ext_of_local_quotient_lift`, without
the quasi-compactness assumption carried by that module's broader descent
context.

`kernel_eq_one_of_center_quotient` applies this equality test to a quotient point
acting trivially after every test refinement. A local lift conjugates every
point trivially after every refinement, so it belongs to the full all-test
centre. The prescribed full-kernel equality then says that its image is one.
`isFaithful_of_center_quotient` applies the existing trivial-kernel criterion to
obtain faithfulness.

`restrict_injective_of_isFaithful` evaluates an equality of restricted actions
at every refinement of the universal acting point and applies faithfulness.
`restrict_injective_of_center_quotient` specializes this to the supplied natural
quotient action. This proves uniqueness of a homomorphism inducing a given
inner action.

`restrictEmbeddingOfCenterQuotient` bundles this restriction map as an actual
embedding from group-scheme homomorphisms `H → A` into automorphic actions of
`H` on `G`. Its application is restriction of the supplied quotient action,
as recorded in `restrictEmbeddingOfCenterQuotient_apply`. The embedding's
image consists of those actions obtained by this restriction.

The base and all test schemes are arbitrary in universe `u`. No reductivity,
connectedness, affineness, smoothness or quasi-compactness hypothesis is used.
Local finite presentation is present in the supplied quotient predicate but is
not used by these equality proofs. The helper supplies the uniqueness part of
Task 6418; it does not prove the existence of an inner factorization.
