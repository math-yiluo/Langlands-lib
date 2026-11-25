# Actual retract images of idempotent field-group maps

For an idempotent endomorphism of a smooth connected affine group over any
field, `idempotentImage` constructs an actual smooth connected affine closed
image together with an inclusion and a projection. Their composite is the
original idempotent and the reverse composite is the identity. The closed
representative equals the original map's pointwise range on every relative
test scheme.

The existing homomorphism image theorem supplies the smooth connected closed
schematic image and a flat surjective projection. This projection is an
epimorphism, so idempotency shows that the endomorphism fixes its image.
Monicity of the inclusion gives the retraction identity, which identifies the
closed image with the full pointwise range.

Conjugation equivariance makes that range normal. For an almost-simple group,
its defining normal-subgroup dichotomy leaves only the trivial or full image.
A trivial image makes the endomorphism the trivial map. A full image makes its
inclusion an isomorphism; since the map fixes this image, it is the identity.
The stronger lemma assumes only that the pointwise image is normal. No
algebraic closedness or characteristic hypothesis is needed, and all
normality tests include nonreduced relative test schemes.

This is internally derived from the existing smooth connected image theorem,
almost-simplicity predicate and represented-subgroup interfaces. It supplies
the field-level normal-idempotent step of Weil-factor rigidity; it makes no
arbitrary-base gluing or product-classification assertion.
