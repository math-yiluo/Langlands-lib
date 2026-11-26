# Haar measures for the twisted van Dijk formula

Module `Langlands.BaseChange.TwistedVanDijk.Measures`. With the notation of
`Langlands.BaseChange.TwistedVanDijk.Groups` (`G = GL_n(E)`, `K = GL_n(𝒪_E)`, a standard block
parabolic `P = M U`, an automorphism `σ` of `E`), it proves the facts about Haar measures used
in the twisted van Dijk formula: invariance under the entrywise action of `σ`, the Iwasawa
decomposition of Haar measure with the normalizations of Henniart–Lemaire, *Changement de base
et induction automorphe pour GL_n en caractéristique non nulle* (2011), II.4.5 (printed p. 86),
and finite coset sums for integrals over a compact group.

## Uniqueness of Haar measure

In a second countable topological group with its Borel σ-algebra:

- `eq_of_isMulLeftInvariant_of_eq_one`: two σ-finite left invariant measures giving mass one to
  the same compact set with nonempty interior are equal (both equal `Measure.haarMeasure`
  normalized on that set, `haarMeasure_eq_iff`).
- `map_eq_self_of_preimage_eq`: a Haar measure `μ` is invariant under an automorphism `θ` of
  topological groups that preserves a nonempty compact open set `C`. Indeed `μ.map θ` is a Haar
  measure, hence `s • μ` for the scalar `s = haarScalarFactor (μ.map θ) μ`, and evaluating on
  `C` (`0 < μ C < ∞`, `(μ.map θ) C = μ (θ⁻¹ C) = μ C`) gives `s = 1`.

## Finite coset sums

`integral_eq_sum_quotient_out`: for a finite left invariant measure `μ` on a group `H`, a
subgroup `H'` of finite index with measurable underlying set, and `f` invariant under right
translation by `H'`,
`∫ f dμ = ∑_{x ∈ H/H'} μ(H') f(out x)`, where `out x` is the chosen representative. Each left
coset `out(x) H'` has mass `μ(H')` by left invariance, `f` is constant on it, and `f` is the sum
of its values times the indicator functions of the cosets.

## Invariance under `σ`

`leviContinuousAut σ B`, `unipotentContinuousAut σ B` and `integralContinuousAut σ n` are the
entrywise actions of `σ` on `M`, on `U` and on `K`, as automorphisms of topological groups
(`entrywiseAut_mem_integralGL` gives the action on `K`). Each preserves a nonempty compact open
set (`K`, `M(𝒪_E) = ∏ GL_{n_i}(𝒪_E)`, `U ∩ K`, and the whole of `K`, by
`entrywiseAut_mem_integralGL_iff`), so `map_eq_self_of_preimage_eq` gives:

- `map_entrywiseAut_eq`: Haar measure on `GL_n(E)` is invariant under `entrywiseContinuousAut`;
- `map_leviAut_eq`, `map_unipotentAut_eq`, `map_integralAut_eq`: the same on `M`, on `U` (a
  closed subgroup of `G`, hence locally compact and second countable) and on `K`.

## Iwasawa decomposition of Haar measure

- `unipotentSubgroup_secondCountable`, `unipotentSubgroup_locallyCompact`,
  `parabolic_secondCountable`, `parabolic_locallyCompact`, `integralGL_compactSpace`,
  `integralGL_secondCountable` record the topological properties used as local instances.
- `parabolicHaar μM μU` is the image of `μM × μU` under `(m, u) ↦ m u`.
  `parabolicHaar_isHaarMeasure`: it is a left Haar measure on `P`. Finiteness on compacts and
  positivity on opens transfer along the homeomorphism `parabolicProductHomeomorph`. For left
  invariance, left multiplication by `m₀ u₀` is, in the coordinates `(m, u)`, the skew product
  `(m, u) ↦ (m₀ m, (m⁻¹ u₀ m) u)` (`parabolicProduct_mul`), which preserves `μM × μU` because
  `μM` is left invariant and each fibre map `u ↦ (m⁻¹ u₀ m) u` preserves `μU`
  (`MeasurePreserving.skew_product`).
- `iwasawa_measure_eq`: if `μG(K) = 1`, `μM(M(𝒪_E)) = 1`, `μU(U ∩ K) = 1` and `μK` is the Haar
  probability measure of `K`, then `μG` is the image of `(μM × μU) × μK` under
  `((m, u), k) ↦ m u k`, that is, `dg = dm du dk` as in Henniart–Lemaire II.4.5. The Library's
  `CompactFactorization.exists_pos_eq_smul_map_mul_prod`, applied to the closed subgroup `P`,
  the compact subgroup `K` and `G = P K` (`exists_parabolic_mul_integralGL`), gives
  `μG = c · (image of parabolicHaar × μK)` for some `c > 0`. Both sides are evaluated on `K`:
  the preimage of `K` is `(M(𝒪_E) × (U ∩ K)) × K` (`leviEmbedding_mul_mem_integralGL_iff`), of
  mass `1`, so `c = 1`.
