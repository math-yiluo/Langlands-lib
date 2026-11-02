# Actual positive-torus and norm-one adelic factorization

Author: Worker 112.

Let `F` be a number field, `G` an actual group scheme over `Spec F`, `T` an
actual commutative group scheme, and `i : T.toGrp ⟶ G` an actual morphism.
Retain the supplied finite split-torus isomorphism for `T`, injectivity of
`characterRestrict i` on all actual rational characters, and finite index of
its range. The existing normalized logarithm and its explicit positive-torus
section construct the factors; a decomposition is not supplied as an input.

For an actual adelic point `x`, define `positiveFactor x` by applying the inverse
of `positiveAmbientLogEquiv` to `characterLogHom x`. This is a continuous
homomorphism into the intrinsic positive subgroup of the actual adelic points
of `T`. It recovers every intrinsic positive point from its image under `i`,
and sends every actual norm-one point to the identity. Define
`normOneFactor x` as the actual point
`(positivePointMap (positiveFactor x))⁻¹ * x`. Applying the logarithm proves
that this point belongs to the existing `normOneSubgroup F G`.

Multiplication `(a,n) ↦ positivePointMap a * n` is a bijection from the
intrinsic positive subgroup times the actual norm-one subgroup to `G(A_F)`.
Its inverse is precisely `(positiveFactor, normOneFactor)`. Applying the
logarithm recovers the first factor, and cancellation recovers the second.
When the scheme underlying `G` is affine, its existing adelic group operations
are continuous. Both displayed maps are then continuous, giving the
homeomorphism `normOneDecomposition`. No finite-type assumption is needed.

If the actual scheme-theoretic condition `GroupScheme.IsCentral i` holds, its
definition applied to the actual adele test scheme shows that each positive
point image commutes with every ambient adelic point. This commutation proves
that the same multiplication map preserves the ordinary direct product group
law, yielding `normOneDecompositionMulEquiv`. Without this centrality input the
carrier equivalence and, for affine `G`, the homeomorphism still apply.

## Provenance and scope

This is an elementary derived consequence of the actual logarithm section and
its exact norm-one kernel, motivated by MW95 I.1.4, printed pp.5–7, and I.2.1,
printed pp.18–20, especially the number-field choice `Mᶜ = M¹` on p.19.
Source ID `moeglin-waldspurger-1995-spectral-decomposition`, folder SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`.
The implemented proof uses the already constructed continuous logarithm and
inverse positive exponential, followed by explicit multiplication and
cancellation. The degree and finite-index normalizations remain in those
existing maps.

The algebraic existence of a suitable central split torus for a general
connected reductive group and the general injective finite-index restriction
theorem remain separate obligations. The intrinsic positive factor is mapped
by the actual morphism `i`; it is not an abstract substitute for adelic points.
Empty finite rank is allowed. No quotient comparison, Haar normalization,
unimodularity, reduction coverage, or finite-volume theorem is asserted here.
