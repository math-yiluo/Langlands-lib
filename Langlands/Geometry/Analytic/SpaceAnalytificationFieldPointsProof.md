# Base-field points of the analytification of an algebraic space

The theorem proves `SpaceAnalytificationFieldPointsStatement` in every
universe. For a separated algebraic space `X` locally of finite type over
a complete nontrivially normed ultrametric field `K`, the analytification's
full `K`-valued points form a set equivalent to `X(K)`. The underlying point
of the image of `x` is the point specified by `rationalPoint` for each allowed
presentation of `K`. The projection to underlying points is injective.

The published reduction constructs the full analytic point of an algebraic
point from the affine comparison and the map attached to the given point.
It proves projection injectivity using chart character uniqueness over `K`.
The published separatedness argument, applied with underlying-point lifting
for pullbacks, gives injectivity of `rationalPoint`.

For surjectivity, choose an ordinary point in an étale affine test lying
above the projection of the given full `K`-point. At that chosen source
point, the finite étale chart calculation yields a finite separable completed
residue. The normal closure construction and full chart character extension
supply a full analytic point there valued in a finite Galois extension `L/K`.
Recover its algebraic coordinates as a map `A →ₐ[K] L` from the chart's
coordinate algebra.

Embed `L` into a complete algebraically closed ultrametric extension of `K`.
This embedding and its composites with `K`-automorphisms of `L` are
isometric. Postcomposition preserves the underlying point while it changes
the coordinates by the same maps. The images on the analytification agree
as full points by uniqueness over the given full base-field point. Separatedness
represents the algebraic chart self-relation by an affine test. Its analytic
pullback lifts the two full points in the algebraically closed value field.
Naturality of the recovered coordinates gives an algebraic point of the
self-relation with the two specified projections. Algebraic commutativity
identifies their images in `X` over the larger field. Injectivity of coefficient
change for separated spaces gives the same equality over `L`, so finite Galois
descent gives a point of `X(K)`.

The norm of the recovered coordinates is the seminorm of the chosen ordinary
point. Use the affine seminorm comparison to realize the norm of `L` as an
ordinary point of its affine analytification. Its restriction to `A` has the
seminorm of the chosen source point, and its restriction to `K` has the
seminorm of the identity point. Injectivity of the seminorm comparison gives
both analytic point equalities. Naturality of the analytification family and
the algebraic descent equality identify the point of `X(K)` with the given
analytic point under `rationalPoint`. This gives the image premise of the
published reduction and hence the required equivalence.

The residue and fibre-product steps follow the setting of Conrad–Temkin,
*Non-archimedean analytification of algebraic spaces* (2009), Example 2.3.2,
pp. 11–12, registered as `conrad-temkin-2009-nonarchimedean-analytification`.
The Lean proof uses full field-valued points for the conjugate comparison
and the Library's finite Galois descent theorem for the algebraic image.
