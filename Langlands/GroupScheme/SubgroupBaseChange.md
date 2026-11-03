# Base change of represented subgroup functors

This internal transport unit concerns arbitrary morphisms of base schemes and
the existing subgroup functors on all test schemes.

`SubgroupFunctor.baseChangeCarrierEquiv` restricts the pullback point equivalence
to the subgroup carriers. For every test scheme over the new base, it is a
group isomorphism from the points of the base-changed subgroup to the points
of the original subgroup on that test scheme regarded over the original base.
Its forward map is the ambient point equivalence, and its inverse is the
ambient inverse with subgroup membership supplied by the inverse identity.

`SubgroupFunctor.range_baseChangeHom` states that the range of the base-changed
group homomorphism equals the base change of its range. Its equality is the
reverse of the existing `SubgroupFunctor.range_baseChange` in
`Absolute.ParabolicTransport`, whose orientation is unchanged.
The proof uses the pullback point equivalence in both directions, including
its compatibility with composition. In particular, this is an equality of
pointwise images, not an assertion about a scheme-theoretic image.

Base change preserves the full subgroup functor, the identity subgroup functor,
intersection, and normalization. Normalization follows because the pullback
point equivalence preserves products and inverses. Normality is its specialization
to normalization by the full subgroup functor.

If a group homomorphism represents a subgroup functor, its base change represents
the base-changed functor. The monomorphism is preserved by the pullback functor;
the range equality is the preceding range calculation.

Closed subgroup inclusions remain closed under base change. The proof obtains
the pullback square for the underlying homomorphism by cancellation of the
outer and right pullback squares, then applies stability of closed immersions.

For dynamic centralizers the existing `Dynamic.centralizer_baseChange` then
identifies this representative with a representative of the centralizer of the
base-changed cocharacter. No cocharacter is excluded, and no affineness,
smoothness, connectedness or reductivity assumption is imposed.

All assertions are derived directly from the published definitions and the
published pullback point equivalence. This unit does not prove the reductivity
of dynamic centralizers.
