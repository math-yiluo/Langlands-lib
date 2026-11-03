# Exact products of subgroup functors

Author: Worker 1291.

This is an internal elementary construction on the existing
`Langlands.GroupScheme.SubgroupFunctor` architecture. It introduces no structural
theorem about reductive groups. All definitions and lemmas hold over an arbitrary
base scheme in an arbitrary universe `u`, on every scheme over that base,
including nonreduced test schemes.

`IsPointwiseProduct F A B` means that a point belongs to `F(T)` exactly when it
is `a * b` for `a ∈ A(T)` and `b ∈ B(T)`. Both factors are over the original
test scheme. There is no localization, sheafified image, generated subgroup or
rational-point-only interpretation.

`normalizedProduct A N hN` constructs this exact product as a subgroup functor
when the existing all-test predicate `N.IsNormalizedBy A` holds. Its carrier is
the displayed existential condition. Closure under multiplication moves the
first point of `N` past the second point of `A` by conjugation; closure under
inversion uses `a⁻¹ (a n⁻¹ a⁻¹)`. Restriction commutes with multiplication and
preserves each factor. `mem_normalizedProduct` and
`normalizedProduct_isPointwiseProduct` expose the defining condition.

The other lemmas give uniqueness of a functor with these exact product
carriers, the inclusions of the two factors, the universal inclusion in a
subgroup containing both factors, monotonicity, and monotonicity of the existing
all-test image. `mem_map_comap_iff` restates the existing `map_comap` theorem as
membership in the intersection with the range. It does not claim that a range
or product is represented by a scheme.

The provenance is derived internal group theory and restriction naturality.
The later parabolic-in-Levi correspondence will use these operations to state
the structural assertions of Renard V.3.11 and Borel–Tits 4.4(c); those
assertions are not proved in this module.
