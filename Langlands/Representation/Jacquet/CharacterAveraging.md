# Character-twisted averaging over compact open subgroups

This module proves general facts about averaging a smooth representation
against a character over compact open subgroups. It is an internal helper for
the proof of the JPSS (1983) Section (4.5) deformation lemma
(`Langlands.RankinSelberg.twoBlockWhittakerDeformation`). It plays the role of
the averaging operators `P_{ψ,N_0}` in Casselman–Shalika (1980), Section 2,
and of the compact-open exhaustion in Shahidi (1978), Proposition 3.2. The
statements here are general: they do not depend on any particular group or
representation. All declarations are in `Langlands.Jacquet.Localization`.
Author: Worker 831.

## Orbit means

For a representation `π` of a group `H` and a vector `v` with finite orbit,
the Library's `Compact.orbitMean π v` is the normalized sum of the distinct
orbit points. This module adds:

- `orbitMean_eq_smul_sum`: the orbit mean as `card⁻¹ • ∑ x`.
- `orbitMean_mem`: the orbit mean lies in any submodule containing the orbit.
- `apply_orbitMean`: a linear form that takes the value `ℓ v` on every orbit
  point takes the same value on the orbit mean.
- `sub_orbitMean_mem`: if every `v - π g v` lies in a submodule `S`, then so
  does `v - orbitMean π v`. The proof writes `v - mean` as the normalized sum
  of the differences `v - x` over the orbit.
- `orbit_apply`, the imported `Compact.orbitMean_apply`: a translate `π g v` has the same orbit, so
  the same orbit mean.
- `orbitMean_eq_quotient_sum`: if a subgroup `K` of finite index fixes `v`,
  the orbit mean is `card(H/K)⁻¹ • ∑_{c ∈ H/K} π(c.out) v`, for any choice of
  representatives. The map `c ↦ π(c.out) v` is an `H`-equivariant map from
  `H/K` onto the orbit, and the Library's `finiteMean_comp` gives equality of
  the normalized sums.

## The twisted average `P_H`

Fix a topological group `G`, a representation `ρ` of `G` on a complex vector
space `V`, a subgroup `N` and a character `χ : N →* ℂˣ` whose kernel is open
in `N`.

- `twistedRestriction ρ N χ` is the representation `n ↦ χ(n)⁻¹ ρ(n)` of `N`,
  built with the Library's `twist`. `twistedRestriction_apply` gives this
  formula.
- `isSmooth_twistedRestriction`: if `ρ` is smooth, then so is the twisted
  restriction. The restriction to `N` is smooth (pull back the stabilizers),
  and the Library's `isSmooth_twist_iff` handles the twist by a character with
  open kernel.
- `characterAverage hρ hχ H hH` is the Library's `averageMap` of the twisted
  restriction over a compact open subgroup `H` of `N`. As a linear map
  `V → V`, it sends `v` to the orbit mean of `v` under
  `h ↦ χ(h)⁻¹ ρ(h)`, `h ∈ H` (`characterAverage_eq_orbitMean`).

Properties of `P_H`:

- `characterAverage_mem`: `P_H` maps every `ρ(N)`-stable submodule into
  itself.
- `apply_characterAverage`: if `ℓ (ρ n v) = χ n * ℓ v` for all `n ∈ H`, then
  `ℓ (P_H v) = ℓ v`. In particular `functional_characterAverage`: every
  `χ`-equivariant functional is unchanged by `P_H`.
- `sub_characterAverage_mem`: `v - P_H v` lies in the character relations
  `relations ρ N χ`, i.e. the span of `ρ(n) w - χ(n) w`.
- `characterAverage_relation`: `P_H` kills `ρ(n) w - χ(n) w` for `n ∈ H`,
  because `ρ(n) w = χ(n) τ(n) w` for the twisted action `τ` and the orbit mean
  of a translate equals the orbit mean.
- `characterAverage_eq_quotient_sum`: if a finite-index subgroup `K` of `H`
  fixes `v` under the twisted action, then
  `P_H v = card(H/K)⁻¹ • ∑_{c ∈ H/K} χ(c.out)⁻¹ • ρ(c.out) v`.

## Exhaustions, extension and spanning

Now let `S : ℕ → OpenSubgroup N` be a monotone sequence of compact open
subgroups covering `N`.

- `eventually_characterAverage_eq_zero`: for every relation `r`, there is
  `k₀` with `P_{S k} r = 0` for all `k ≥ k₀`. Proof by induction on the span:
  for a generator `ρ(n) w - χ(n) w`, take `k₀` with `n ∈ S k₀` and use
  monotonicity; sums use the maximum of the two indices.

Let `V'` be a `ρ(N)`-stable submodule and `J' : V' → ℂ` a linear form with
`J'(ρ(n) v) = χ(n) J'(v)` for all `n ∈ N`, `v ∈ V'`.

- `apply_eq_zero_of_mem_relations`: `J'` vanishes on every relation lying in
  `V'`. Extend `J'` arbitrarily to a linear form `ℓ` on `V`; `ℓ` is
  `χ`-equivariant on the orbit of `v ∈ V'`, so `ℓ(P_{S k} v) = ℓ(v)`, and
  for a relation `v` the left side is `0` for large `k`.
- `exists_functional_extension`: a linear form on `V'` that vanishes on the
  relations in `V'` is the restriction of a `χ`-equivariant functional `J` on
  `V` (an element of the Library's `Whittaker.functionals N χ ρ`). The form
  descends to the image of `V'` in `V / relations`; extend that by linear
  algebra (`LinearMap.exists_extend`) and compose with the quotient map.
  This lemma does not use the exhaustion or any topology.
- `relations_sup_eq_top`: if, in addition, `J' ≠ 0` and the
  `χ`-equivariant functionals form a space of dimension at most one (every
  functional is a scalar multiple of every nonzero one), then
  `relations ρ N χ ⊔ V' = ⊤`. Otherwise a nonzero linear form `φ` vanishing on
  `relations ⊔ V'` exists (`Submodule.exists_le_ker_of_lt_top`); it is
  `χ`-equivariant, hence `φ = c • J` for the extension `J` of `J'`, and
  evaluating at a vector of `V'` where `J' ≠ 0` forces `c = 0`, so `φ = 0`.
- `eventually_characterAverage_mem`: when `relations ρ N χ ⊔ V' = ⊤`, every
  vector `F` satisfies `P_{S k} F ∈ V'` for all large `k`. Write `F = r + v`
  with `r` a relation and `v ∈ V'`; the averages eventually kill `r` and
  preserve `V'`.

## Scope

No admissibility, irreducibility, finite-dimensionality or topology on `V` is
used. Smoothness of `ρ` and openness of the kernel of `χ` give finite orbits
under compact open subgroups, which is all the averaging needs. The uniqueness
hypothesis in `relations_sup_eq_top` is an explicit premise of that lemma.

`Compact.orbitMean_apply` is reused from [OrbitMeanTranslation](../Compact/OrbitMeanTranslation.md).
