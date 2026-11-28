# Injectivity of Hecke means from a support condition

Module `Langlands.BushnellKutzko.SplitTypeJacquet.HeckeSupport`.

Throughout, `J` is a subgroup of a group `G`, `ρ : Representation ℂ J W`, `π : Representation ℂ G V`
and `Φ : ρ.IntertwiningMap (π.comp J.subtype)`. Intertwining spaces `I_x(ρ)` and the set
`representationSelfIntertwining ρ` are those of the module `RepresentationIntertwining`. The group
`J` acts on linear maps `W → V` by `F ↦ π(j) ∘ F ∘ ρ(j)⁻¹` (`Representation.linHom`). The **Hecke
mean** of `x ∈ G` and `Θ : W → W` at `Φ` is the orbit mean (`Compact.orbitMean`) of
`π(x) ∘ Φ ∘ Θ` under this action.

## A double coset lemma

`mem_of_mem_doubleCoset`: suppose `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)`, `M` normalizes `U` and `U⁻`,
`M ∩ U = 1`, and an element of `U⁻` that lies in `M U` is trivial. If `d ∈ M` satisfies
`d = j₁ x j₂` with `j₁, j₂ ∈ J` and `x ∈ U`, then `d ∈ J`. Proof: write `j₁ = l m u` and
`j₂ = u' m' l'`. Then `d` times an element of `U⁻` equals an element of `M U`. The `U⁻` part is
trivial, then the `U` part is trivial, and `d = m m' ∈ J`.

## Intertwiners from a retraction

- `retractionIntertwiner`: if `ψ : V → W` satisfies `ψ ∘ π(j) = ρ(j) ∘ ψ` for `j ∈ J`, then for every
  `x ∈ G` the map `ψ ∘ π(x) ∘ Φ` lies in `I_{x⁻¹}(ρ)`.
  `retractionIntertwiner_eq_zero`: so it vanishes when `x⁻¹` does not intertwine `ρ`.
- `exists_equivariant_retraction`: if `J` is compact open, `π` and `ρ` are smooth, `W` is
  finite-dimensional and `Φ` is injective, such a `ψ` exists with `ψ ∘ Φ = id`. The kernel `K₀` of
  `ρ` is open of finite index in `J`. A linear left inverse of `Φ` composed with the averaging
  projection over the image of `K₀` (`Compact.averageMap`) is `K₀`-equivariant. Its average over
  `J/K₀` (`FiniteQuotientAveraging.intertwinerAverage`) is `J`-equivariant and is still a left
  inverse of `Φ`.

## Injectivity at one element

`linHom_fixed`: for `Θ ∈ I_x(ρ)` and `d ∈ J` with `x⁻¹ d x ∈ J`, the map `π(x) ∘ Φ ∘ Θ` is fixed by
`d`.

`eq_zero_of_heckeMean_eq_zero`: let `ψ` be an equivariant retraction of `Φ` and let `ζ ∈ G` satisfy
the following:
- every `j ∈ J` is `u d` with `u ∈ J ∩ U`, `d ∈ J` and `ζ⁻¹ d ζ ∈ J`;
- `ζ⁻¹ U ζ ⊆ U`;
- the support condition: every `y ∈ U` with `ζ y ζ⁻¹ ∈ J` that intertwines `ρ` lies in `J`.

Let `Θ ∈ I_ζ(ρ)` be such that the orbit of `π(ζ) ∘ Φ ∘ Θ` is finite (the Lean statement takes
this as an instance argument). If the Hecke mean of `ζ` and `Θ` at `Φ` is zero, then `Θ = 0`.
Without finiteness the conclusion fails, since `Compact.orbitMean` is zero on infinite orbits.
Proof: apply the linear
map `F ↦ ψ ∘ π(ζ⁻¹) ∘ F` to the orbit sum. Every orbit point is `u · (π(ζ) ∘ Φ ∘ Θ)` with
`u ∈ J ∩ U`. If the point differs from `π(ζ) ∘ Φ ∘ Θ`, then `x = ζ⁻¹ u ζ ∉ J`, so by the support
condition `x⁻¹` does not intertwine `ρ`, and the image `(ψ ∘ π(x) ∘ Φ) ∘ Θ ∘ ρ(u)⁻¹` is zero. The
remaining point maps to `ψ ∘ Φ ∘ Θ = Θ`.

## Composition and powers

The results of this section, except the general orbit-mean lemmas and the statements about
`IsIntertwinerAt` and `IsTypeContraction` alone, assume that every orbit of `J` on linear maps
`W → V` is finite (hypothesis `hfin`).

- `meanLin`: the orbit mean as a linear map when all orbits are finite. `orbitMean_apply_eq`:
  translating a vector does not change its orbit mean. `orbitMean_fixed`: a mean over a finite
  orbit is fixed by the group. `orbitMean_of_fixed`: the mean of a fixed vector is the vector.
- `equivariant_of_fixed`, `intertwiningOfEquivariant`: a linear map fixed by the action is
  `J`-equivariant and defines an intertwiner.
- `heckeMean_comp`: suppose all orbits are finite and every point of the orbit of `F = π(ζ^r) ∘ Φ ∘ Θ'` is `u · F` with
  `u ∈ J` and `ζ u ζ⁻¹ ∈ J`, and that `Θ ∘ ρ(ζ u ζ⁻¹) = ρ(u) ∘ Θ` for such `u`. Then the Hecke mean
  of `ζ` and `Θ` applied to the mean of `F` is the Hecke mean of `π(ζ^{r+1}) ∘ Φ ∘ (Θ' ∘ Θ)`. Each
  orbit point, composed with `π(ζ)` and `Θ`, is a translate of `π(ζ^{r+1}) ∘ Φ ∘ (Θ' ∘ Θ)`.
- `IsIntertwinerAt ρ x T`: `T ∘ ρ(x h x⁻¹) = ρ(h) ∘ T` for all `h ∈ J` with `x h x⁻¹ ∈ J`. It is
  the condition for `T` to underlie an element of `I_x(ρ)` (`IsIntertwinerAt.toSpace`,
  `isIntertwinerAt_of_space`). `IsIntertwinerAt.mul_left`: if `T ∈ I_x(ρ)` and `m ∈ J`, then
  `T ∘ ρ(m)⁻¹ ∈ I_{m x}(ρ)`.
- `IsTypeContraction J U M Ubar ζ`: every `j ∈ J` is `u m l` with `u ∈ J ∩ U`, `m ∈ J ∩ M`,
  `l ∈ J ∩ U⁻`; conjugation by `ζ` and by `ζ⁻¹` preserves `J ∩ M`; `ζ⁻¹ U ζ ⊆ U`,
  `ζ (J ∩ U) ζ⁻¹ ⊆ J ∩ U`, `ζ U⁻ ζ⁻¹ ⊆ U⁻` and `ζ⁻¹ (J ∩ U⁻) ζ ⊆ J ∩ U⁻`. The element `ζ` need not
  commute with `J ∩ M`.
  `upper_pow`, `lower_pow`, `levi_pow`, `levi_pow'` and `lowerNorm_pow` give the corresponding
  properties of the powers of `ζ`. `convex`: if `x ∈ J` and `ζ^n x ζ^{-n} ∈ J`, then
  `ζ^t x ζ^{-t} ∈ J` for all `t ≤ n`; the `U⁻`-component of `x` is controlled through
  `ζ^n (·) ζ^{-n}`. `factor_stab`: every `j ∈ J` is `u d` with `u ∈ J ∩ U` and
  `ζ^{-k} d ζ^k ∈ J`.
- `IsTypeContraction.pow_intertwiner`: `Θ ∈ I_ζ(ρ)` implies `Θ^k ∈ I_{ζ^k}(ρ)`, by `convex`.
- `IsTypeContraction.iterate_heckeMean`: if all orbits are finite and `Θ ∈ I_ζ(ρ)`, the
  `(k+1)`-fold iterate of
  `F ↦ mean(π(ζ) ∘ F ∘ Θ)` at `Φ` is the Hecke mean of `ζ^{k+1}` and `Θ^{k+1}`.
- `IsTypeContraction.heckeMean_pow_eq_zero`: if all orbits are finite, `Θ ∈ I_ζ(ρ)`, and the
  Hecke mean of `ζ` and `Θ` is injective on
  equivariant maps, then the Hecke means of `ζ^k` and `Θ^k` are injective on intertwiners.
  The iterates are equivariant because orbit means are fixed.

## Main results

- `IsTypeContraction.heckeMean_injective`: let `J` be compact open, `π` and `ρ` smooth, `W`
  finite-dimensional, `ρ` irreducible and all orbits of the action on `W → V` finite. Let `ζ` be a
  type contraction satisfying the support condition and `Θ ∈ I_ζ(ρ)` nonzero. Then for every `k`,
  if the Hecke mean of `ζ^k` and `Θ^k` at `Φ` is zero, then `Φ = 0`. A nonzero equivariant
  `F` is injective by irreducibility. It has an equivariant retraction, so
  `eq_zero_of_heckeMean_eq_zero` would force `Θ = 0`.
- `heckeMean_mul_left`: the Hecke mean of `m x` and `T` equals the Hecke mean of `x` and
  `T ∘ ρ(m)`, for `m ∈ J`.
- `IsTypeContraction.heckeMean_injective_translate`: under the same hypotheses, let `m ∈ J`
  commute with `ζ`. For every `e` and `r` there is `Θ' ∈ I_{(m ζ^e)^r}(ρ)`, namely
  `Θ^{er} ∘ ρ(m^r)⁻¹`, whose Hecke mean is injective on `Hom_J(ρ, π)`.

## Source

The support condition and the use of an element `ζ` that is a power of a prime element of `E` on
one block are modelled on the proof of Lemma (8.3.10) of C. J. Bushnell and P. C. Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), printed pp. 294–295 (PDF
pp. 306–307), source ID `bushnell-kutzko-1993-admissible-dual-gln`. There, an element in the
support of a convolution is shown to lie in the group by an intertwining argument, and the
support of the `k`-fold convolution is computed from Iwahori decompositions. The proof here works
with intertwiners and orbit means instead of the Hecke algebra: the support condition is used
through an equivariant retraction rather than through invertibility of Hecke algebra elements.
