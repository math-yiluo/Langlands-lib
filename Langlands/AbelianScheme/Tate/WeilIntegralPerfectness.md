# Integral perfectness of the Weil pairing at algebraically closed points

This internal module derives integral perfectness of the existing Weil
pairing from the published nondegeneracy of the finite Weil pairing at
geometric points. It adds no literature assertion and no new premise. All
dual, Poincaré, tensor and Picard inputs and the relative transition
statement `RelativeFiniteWeilTransitionStatement` are explicit arguments, as
in the imported constructions `integralWeilBilinearMap` and
`rationalWeilBilinearMap`.

## Torsion-freeness of the integral Tate twist

In `Langlands.TateTwist.Divisibility`, `full_eq_zero_of_nsmul_eq_zero` shows
that a positive integer `k` acts injectively on the full integral Tate twist
of any commutative ring. If `k • x = 0`, the `n`-th coordinate of `x` is
the transition of its `n k`-th coordinate. That transition is the `k`-th
power, and the `k`-th power of the `n k`-th coordinate is the corresponding
coordinate of `k • x`, which is zero. `full_toRational_injective` deduces
that the twist embeds in its rationalization `ℚ ⊗[ℤ] Full`. The kernel of
this localization map consists of elements killed by a nonzero integer. The
proof is the same as the published `GroupScheme.Tate.full_toRational_injective`
for Tate groups.

## The integral dual and its perfectness

`weilIntegralDual T` is the definition of the module. For a test object `T`,
it is the additive subgroup of the full rational Tate module of the
constructed dual consisting of those `y` such that the rational Weil
pairing of `y` with the image of every integral Tate vector of `A` lies in
the image of the integral Tate twist. `mem_weilIntegralDual` unfolds
membership.

`integralWeil_exists_nsmul_of_forall` is the integral form of perfectness.
The point `s` is a `K`-point with `K` algebraically closed of characteristic
zero, and every positive integer is a unit on `S`. Let `y` be an integral
dual Tate vector whose integral Weil pairing with every integral Tate vector
of `A` is `N` times an element of the twist. The level-`N` coordinate of that
pairing is the finite Weil pairing of the level-`N` coordinates, by
`evaluation_integralWeilValue`, and it is zero because the level is killed by
`N`. Every level-`N` torsion point of `A` at `s` lifts to an integral Tate
vector (`Tate.full_evaluation_surjective_at`). Hence the level-`N`
coordinate of `y` pairs trivially with all of `A[N]`. It is zero by the right
half of the published `geometricFiniteWeilNondegeneracy`. Finally
`GroupScheme.Tate.full_exists_nsmul_of_evaluation_eq_zero` writes `y` as `N`
times an integral vector.

`weilIntegralDual_eq_range` states perfectness at such a point: the integral
dual equals the image of the integral dual Tate group. Every element of the
image pairs integrally, by `rationalWeilBilinearMap_toRational`. Conversely,
write `c • y` as the image of an integral `y0` for a nonzero integer `c`,
which is possible because the rationalization is a localization. For each
integral vector `x`, the pairing of `x` with `y0` and `c` times an integral
twist element have the same rational image. By injectivity of the twist
rationalization they are equal. Writing `c = sign(c) |c|`, the integral form
gives `y0 = |c| • y1`. Then `c` times the image of `sign(c) • y1` is the image
of `y0`, which is `c • y`. Cancelling `c` in the rational vector space gives
`y` as the image of `sign(c) • y1`.

## Integrality of rational dual-valued homomorphisms

`exists_ofHom_eq_of_weilIntegral` assumes in addition that the base is
connected and locally noetherian, and it takes the finite-étale torsion
statement. Let `r` be a rational homomorphism from `A` to its constructed
dual `DA`. Suppose the rational Weil pairing of `x` with the rational Tate
image under `r` of `x'` is integral for all integral Tate vectors `x, x'` at
`s`. Then `r` is the rationalization of an actual homomorphism `A ⟶ DA`. By
perfectness, the image under `r` of every integral Tate vector is integral.
The published `Tate.exists_ofHom_eq_of_full_image` then removes the
denominators of `r`.

This module states no result about degrees, polarizations or level
structures.
