# Finite Fourier inversion in one variable

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Jacquet and Shalika
(1985, §4.4, condition (6), printed page 328) prescribe the Fourier transform of the first
component `φ` of the test function: on units it is a character, and it vanishes off the units.
In the Library the test vector is a finite sum of translates. This module therefore constructs
`φ` as a finite exponential sum whose transform is any prescribed function on `O` periodic
modulo `ϖ^b O`, by inverting the finite Fourier transform on `O / ϖ^b O`. The specific character
used in the application is fixed by the Library conventions in the final assembly. The canonical
topology, valuation and Borel structure of the p-adic field are local instances.

- `integral_periodic_eq_sum`: for additive subgroups `L ≤ K` of an abelian group with a right
  invariant measure, `L` measurable of finite measure, finite representatives `T ⊆ K` of
  `K / L`, and an `L`-periodic `φ`: `∫_K φ = vol(L) Σ_(t ∈ T) φ(t)`. Proof: `K` is the disjoint
  union of the translates `t + L`, each of measure `vol(L)`.
- `sum_reps_shift`: in the same setting, with `μ(L) > 0`, `Σ_(t ∈ T) g(t + δ) = Σ_(t ∈ T) g(t)`
  for every `L`-periodic `g` and `δ ∈ K`. Both sides are `vol(L)⁻¹ ∫_K g`, by
  translation invariance of the measure.
- `scaledIntegers F a = {u : a u ∈ O} = a⁻¹ O`, open (`isOpen_scaledIntegers`) and compact
  (`isCompact_scaledIntegers`). It contains `O` when `a` is integral
  (`integer_le_scaledIntegers`).
- `sum_reps_character`: for `ψ` of conductor `O`, `a` integral, representatives `T₁` of
  `a⁻¹ O / O` and integral `t`: `Σ_(u ∈ T₁) ψ(u t) = |T₁|` if `t ∈ a O` and `0` otherwise.
  Proof: the sum is `vol(O)⁻¹ ∫_(a⁻¹ O) ψ(u t) du` by `integral_periodic_eq_sum`. The integral
  is `vol(a⁻¹ O)` or `0`, by the published `subgroup_character_integral_of_trivial` and
  `subgroup_character_integral_of_nontrivial`; the second case uses the conductor property
  `HasIntegerConductorAt.nontrivial`.
- `exists_unit_inversion`: if `S₁` is periodic modulo `a O` on `O`, there are a finite
  `T₁ ⊆ a⁻¹ O` and `Φ₁` with `Σ_(u ∈ T₁) Φ₁(u) ψ(u ξ) = S₁(ξ)` for all integral `ξ`. Explicitly,
  `Φ₁(u) = |T₁|⁻¹ Σ_(y ∈ R) S₁(y) ψ(-u y)` with `R` representatives of `O / a O`. The proof
  combines `sum_reps_character` with `sum_reps_eq` (CosetRepresentatives).
