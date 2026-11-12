# The separation property for the band unitary form

Module: `Langlands.Automorphic.CuspidalAdmissible.Separation`. Provenance: internal; the
analytic step of the classical argument that cusp forms with controlled derivatives form a
finite-dimensional space, written in the energy formulation used by
`isJointlyAdmissible_of_separating`.

## Elementary lemmas

- `setLIntegral_le_add_sum`: if `t ⊆ K ∪ ⋃_i R_i` (finitely many `i`), then
  `∫_t f ≤ ∫_K f + ∑_i ∫_{R_i} f`.
- `exists_exp_small A hA K₀ hK₀`: for finite `A` there is `T ≥ max(0, K₀)` with
  `exp(-(T - K₀))² · A ≤ 1/4` (take `T = K₀ + log(4A + 1)`).
- `exists_eps_small A hA`: for finite `A` there is `ε > 0` with `ε · A ≤ 1/4`.
- `nonpos_of_le_two_quarters`: `r ≥ 0` and `r ≤ r/4 + r/4` give `r ≤ 0`.
- `point_rational_mul_mem_band`: rational left translates keep the band (product formula,
  `determinantNorm_rational`).
- `averageFunctional S hU hU0 p`: the complex linear functional
  `e ↦ A_U(e)(p) = average of e(p u), u ∈ U` (additivity via `average_add` and continuity of
  realized functions).

## The three parts

- `exists_compact_estimate_matrix`: `exists_compact_estimate` for `matrixHaarMeasure`, with the
  instances of module `HaarInstances`.
- `exists_compact_part`: for a realization with unitary central character, an open subgroup
  `L`, a compact `Kc` and a finite `A`, there are a compact `U` with positive measure, a finite
  set `P` and a constant `Cn` such that every `L`-invariant `e` with
  `∑_k bandNorm(D_k e) ≤ A · bandNorm e` satisfies
  `∫_Kc |e|² ≤ bandNorm(e)/4 + Cn ∑_{p ∈ P} |A_U(e)(p)|²`.
  Proof: a compact open `L' ≤ L` (Library `exists_compact_openSubgroup_le`); the compact
  estimate gives `K₃`; `exists_lintegral_compact_le` bounds `∫_{K₃} |D_k e|²` by
  `C₃ · bandNorm(D_k e)`; choose `ε` with `ε C₃ A ≤ 1/4`.
- `exists_cusp_part`: given Siegel finiteness, a cuspidal realization, `L`, Siegel data with
  compact `ΩN`, `C`, compact `Q₁`, `K ≥ 0` and finite `A`, there is `T ≥ 0` such that every
  `L`-invariant `e` with `∑_k bandNorm(D_k e) ≤ A · bandNorm e` satisfies
  `∑_{a > 0} ∫_{cuspRegion … a T} |e|² ≤ bandNorm(e)/4`.
  Proof: `exists_cuspRegion_le` for each block position `a > 0` gives `c₁(a)`; choose `T` with
  `exp(-(T - 2nK))² (∑_a c₁(a)) A ≤ 1/4`.
- `bandNorm_le_siegel`: if every element of `GL_n(𝔸)` has a rational translate in the Siegel
  set `𝔖`, then `bandNorm e ≤ ∫_{𝔖 ∩ band} |e|² d(matrixHaarMeasure)`
  (`lintegral_quotient_le_cover`, `toQuotient_point`).

## Main theorem

`separating_of_bandNorm S hSF hn hS χ hχ hSχ b hb L C`: let `S` be a cuspidal realization of
positive rank with unitary central character, `b` a unitary form with
`bandNorm S f = re b(f, f)` for all `f`. Given Siegel finiteness, for every open subgroup `L`
and every real `C` there are finitely many linear functionals `λ_p` such that every
`L`-invariant `e` with `energy b e ≤ C · re b(e, e)` and `λ_p(e) = 0` for all `p` is zero.

Proof: by `sum_bandNorm_basisDerivative_le_of`, the hypothesis gives
`∑_k bandNorm(D_k e) ≤ A · bandNorm e` with `A = CD · max(C, 0)`. Take the covering Siegel set
of `exists_rational_mul_mem_siegelSetGL`, its torus form (`exists_torus_form`) and the split
(`exists_siegel_band_split`); `exists_cusp_part` gives `T`, and `exists_compact_part` for
`Kc = compactRegion Q₁ (R + n(n(K + T)))` gives `U`, `P`, `Cn`. The functionals are the averages
`averageFunctional S hU hU0 p`, `p ∈ P` (indexed by `Fin #P`). If they vanish at `e`, then
`bandNorm e ≤ ∫_{𝔖 ∩ band} |e|² ≤ ∫_Kc |e|² + ∑_{a>0} ∫_{cusp a} |e|² ≤ bandNorm(e)/4 +
bandNorm(e)/4`; since `bandNorm e = re b(e, e)` is finite, `re b(e, e) ≤ 0`, so `e = 0`.
