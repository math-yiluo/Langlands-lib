# The deformed Whittaker coefficients of flat sections are entire

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

Author: Worker 831.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement` (JPSS 1983,
Section (4.5)). It states and proves the holomorphy input used by the
assembly module `TwoBlockDeformationAssembly`.

## Provenance

This is the holomorphy step of JPSS 1983 (source ID
`jpss-1983-rankin-selberg`), Section (4.5), printed pages 408–409, which
refers to Casselman–Shalika (source ID `casselman-shalika-1980-whittaker`),
Section 2, for the analytic continuation. The proof below follows the
countability argument of Casselman–Shalika, Section 2, Step 2: for each
parameter some averaging level works, one level works for uncountably many
parameters, and holomorphy extends it to all parameters. The formulation
through the character relations and compact-radical sections, and the
explicit exponential-sum formula for the averages, are internal to this
proof; the sources do not state them as numbered results.

## Setting

`F` is a `p`-adic field with its canonical topology, `h : ∑ i, (m i + 1) = t + 1`,
`σ i` are arbitrary complex representations of `GL(m i + 1, F)`, `ψ` is a unitary
additive character, `ρ_u = twoBlockDeformedInduced F m h σ u` is the lower
normalized induction of the blocks twisted by `|det|^u` on the first block,
`N = upperUnipotent (t + 1) F` and `θ⁻¹ = inverseStandardCharacter ψ t`. For a
section `v₀` of `ρ_0`, `f_u = flatSection F h σ u v₀` is the flat family with
underlying function `x ↦ κ(x)^u v₀(x)`, `κ = blockZeroNorm F h`
(`flatFunction`, from `TwoBlockDeformationFlat`).

## `FlatCoefficientDifferentiable F h σ ψ` (definition)

For every measurable structure on `F`, block functionals `ell`,
opens-measurable measure `μ` on the upper radical that is finite on compact
sets, and inverse-character functionals `J u` on `ρ_u` such that

- `J u` agrees with `jacquetFunction ψ ell μ f 1` (JPSS (4.6.2) at the
  identity) on every section `f` of `ρ_u` with compactly supported restriction
  to the upper radical (`compactRadicalSubmodule`), and
- the character relations of `ρ_u` and those compact-radical sections span
  `ρ_u`, for every `u`,

the function `u ↦ J_u(ρ_u(g) f_u)` is differentiable on `ℂ` for every section
`v₀` of `ρ_0` and every `g`.

## Section `Average`

- `unipotentExhaustion F n k`: a chosen increasing exhaustion of
  `upperUnipotent n F` by compact open subgroups (from
  `exists_upperUnipotent_exhaustion` in `TwoBlockDeformationAnalysis`), with
  `isCompact_unipotentExhaustion`, `monotone_unipotentExhaustion` and
  `exists_mem_unipotentExhaustion`.
- `sectionEval_sum`: evaluation of a finite sum of sections is the sum of the
  evaluations.
- `deformedAverage F h σ ψ u k`: the `θ`-twisted average
  `Jacquet.Localization.characterAverage` of `ρ_u` over the `k`-th subgroup of
  the exhaustion (from `Langlands.Representation.Jacquet.CharacterAveraging`).
- `functional_deformedAverage`: every inverse-character functional takes the
  same value on a section and on its average (`functional_characterAverage`).
- `exists_deformedAverage_mem`: if the relations and the compact-radical
  sections span `ρ_u`, every section is averaged into the compact-radical
  sections at some level `k` (`eventually_characterAverage_mem`; the
  compact-radical sections are stable under `N` by
  `inducedRep_mem_compactRadicalSubmodule`).
- `inducedRep_flatSection_of_mem`: if `g⁻¹ n g` lies in the uniform
  stabilizer `flatStabilizer F h σ v₀`, then `ρ_u(n)` fixes `ρ_u(g) f_u` for
  every `u` (`flatFunction_mul_flatStabilizer`).
  `inv_smul_inducedRep_flatSection_of_mem` is the same statement multiplied
  by the inverse of a character value equal to `1`, in the form required by
  `characterAverage_eq_quotient_sum`.
- `exists_deformedAverage_formula F h σ ψ v₀ g k`: there are a finite type
  `ι`, elements `d i` of `GL(t + 1, F)` and scalars `a i`, independent of `u`,
  such that for all `u` and `y`
  `(P_k ρ_u(g) f_u)(y) = ∑_i κ(y d_i)^u • (a_i • v₀(y d_i))`,
  where `P_k = deformedAverage F h σ ψ u k`.
  Proof: let `H` be the `k`-th subgroup and `K ≤ H` the intersection of the
  preimage of `flatStabilizer F h σ v₀` under `n ↦ g⁻¹ n g` with the kernel of
  `θ⁻¹` on `H`. It is open, hence of finite index in the compact group `H`
  (`Subgroup.quotient_finite_of_isOpen`), and every element of `K` fixes
  `ρ_u(g) f_u` for all `u`. By `characterAverage_eq_quotient_sum`,
  `P_k ρ_u(g) f_u = |H/K|⁻¹ ∑_c θ(n_c) ρ_u(n_c g) f_u` over coset
  representatives `n_c`; evaluating at `y` gives the formula with
  `d_c = n_c g` and `a_c = |H/K|⁻¹ θ(n_c)`.

## Section `Main`

`flatCoefficientDifferentiable : FlatCoefficientDifferentiable F h σ ψ`.

Fix `ell`, `μ`, `J`, the two hypotheses, `v₀` and `g`, and write
`F_u = ρ_u(g) f_u`, `P_{u,k} = P_k F_u`. Let `E R` be a compact exhaustion of
the space of radical matrices (`exists_matrix_exhaustion`), and
`X k R` the set of `u` such that the restriction of `P_{u,k}` to the upper
radical vanishes outside `E R`.

1. Every `u` lies in some `X k R`: by `exists_deformedAverage_mem` some
   `P_{u,k}` has compactly supported radical restriction, and its support lies
   in some `E R`.
2. Hence some `X k R` is uncountable, since `ℂ` is not countable
   (`not_countable_complex`) and the union of all `X k R` is `ℂ`.
3. Fix such `k, R` and the formula of `exists_deformedAverage_formula` for
   this `k`. Write `r(x) = upperRadical h F x`. At a radical point `x`, the
   restriction of `P_{u,k}` is `∑_i β_i(x)^u • w_i(x)` with
   `β_i(x) = κ(r(x) d_i) > 0` and `w_i(x) = a_i • v₀(r(x) d_i)` independent
   of `u`. For `x ∉ E R` this sum vanishes for every `u` in the
   uncountable set `X k R`, hence for every `u`
   (`sum_cpow_smul_eq_zero_of_not_countable`). So `X k R = ℂ`, and
   `P_{u,k}` is a compact-radical section for every `u`.
4. For every `u`, `J_u(F_u) = J_u(P_{u,k}) = jacquetFunction ψ ell μ P_{u,k} 1`
   (`functional_deformedAverage` and the first hypothesis). The integrand
   vanishes off `E R`, so the integral is the set integral over `E R`, and by
   the formula it equals `∑_i ∫_{E R} α_i(x) β_i(x)^u dμ` with
   `α_i(x) = a_i ⟨v₀(r(x) d_i), ⊗ ell⟩ · positiveKernel ψ x` continuous and `β_i`
   locally constant (`isLocallyConstant_blockZeroNorm`).
5. Each term is entire by `differentiable_setIntegral_mul_cpow` (from
   `TwoBlockDeformationAnalysis`), so the finite sum is entire.
