# Changing the minimal parabolic with the same Iwasawa compact

`RationalXiChangeMinimalStatement.{u}` is a
Prop-valued statement at arbitrary universe `u`, proved by
`rationalXiChangeMinimal`. Let `F` be a nonarchimedean local field in
universe `u` and `G` an affine, locally finite type, connected reductive
group scheme over `F`. Fix a maximal split torus of `G` and two generic
cocharacters `ν` and `ξ` of that torus. Write `Pν` and `Pξ` for their
minimal standard parabolics. For every compact open subgroup `K` of `G(F)`
with `G(F) = Pν(F) K`, the proposition supplies the factorization
`G(F) = Pξ(F) K` with the same `K`. The two `rationalXi` functions for
these factorizations agree at every point of `G(F)`.

The factorization transport uses only subgroup products and conjugacy.
In a group `H`, inversion takes `H = P K` to `H = K P`. If
`n P n⁻¹ = Q`, write `n = k p` with `k` in `K` and `p` in `P`.
Conjugation by `p` preserves `P`, so `Q = k P k⁻¹`. Conjugation by `k`
preserves `K` and transports the original factorization to `H = Q K`.

For the spherical function, the generic argument restricts conjugation by
`k` to a continuous group isomorphism from `P` to `Q`. The published
`modularCharacter_continuousMulEquiv` identifies their modular characters.
The existing `xi_map` transports the normalized compact Haar integral,
and bi-invariance under `K` removes the conjugation by `k`. The resulting
identity has no scalar normalization factor.

On actual rational points, the published
`MinimalParabolicDistanceLength.exists_map_conj_eq` supplies a rational
normalizer point conjugating the dynamic parabolics of two generic
cocharacters. The published standard/dynamic endpoint comparison identifies
these with the empty-face standard parabolics. The preceding algebraic
argument replaces the rational conjugator by one in `K`. Closedness gives
local compactness of both parabolics, and
`rationalMinimalModulus_eq_modularCharacter` supplies the two inducing
characters. The spherical equality uses compactness and openness of `K`
in `rationalMinimalModulus_eq_one` to show that the new inducing character
is trivial on `Pξ(F) ∩ K`. The theorem `rationalXi_changeMinimal` then
applies the generic transport on `G(F)`.

This derived Library result uses the spherical-function construction and
change of minimal parabolic in Waldspurger (2003), II.1 (printed pp. 251–252)
and the remark after Proposition II.4.5 (printed p. 263). The source is
registered as `waldspurger-2003-plancherel` with SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
