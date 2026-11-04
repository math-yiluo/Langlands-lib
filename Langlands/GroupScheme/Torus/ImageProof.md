# The schematic image of a torus is a torus

This proof is an internal composition of the actual schematic-image group
construction, the published split-torus dominant image factorization, and
comparison of closed dominant factorizations. Its target is
`Langlands.GroupScheme.TorusImageClosedTorusStatement`. The original statement
motivates this as the closed-image and torus-quotient consequence of Milne 5.39
and section 12.e; the implemented route uses a splitting extension instead.

`IsTorus.isTorus_schematicImage` starts with an actual torus `E` over an arbitrary
field `k`, an affine target `H`, and a quasi-compact homomorphism `e : E ⟶ H`.
The group scheme `SchematicImage.image e` is the actual scheme-theoretic image,
with closed inclusion and a quasi-compact schematically dominant projection.
Take the same-universe splitting field supplied by `IsTorus E`. Flat base change
preserves schematic dominance of the projection, and arbitrary base change
preserves the closed inclusion and its factorization equation.

Over the splitting field, the existing split-torus image theorem supplies a
closed split torus and a schematically dominant factorization of the same
base-changed homomorphism. The comparison theorem identifies these two actual
intermediate groups by a group-scheme isomorphism. Transporting splitness along
that isomorphism proves that the original schematic image becomes split over
this field, which is precisely `IsTorus` of that original image.

`torusImageClosedTorusStatement` proves the exact proposition. A torus is
quasi-compact, and the affine target is quasi-separated, so its homomorphism to
the target is quasi-compact. Apply the image result, bundle the image's
commutativity using `IsTorus.isCommMonObj`, and return the original closed
inclusion and projection. Their composite is exactly `e`. The proof retains
every field and universe, the original objects and homomorphism, and the
scheme structure of the image. It does not need the smoothness assumption on
the target, though that assumption is retained by the exact target proposition.

This result supplies one torus-image prerequisite of maximal-torus base change.
It does not assert maximal-torus ascent or the fixed-torus parabolic
classification.
