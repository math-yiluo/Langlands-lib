# Auxiliary analysis for the two-block deformation

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

Author: Worker 831.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement` (JPSS 1983,
Section (4.5)). It collects general facts in complex analysis, integration
and the topology of the upper unipotent group that the analyticity argument
uses. None of them mentions sections or Whittaker functionals.

## Provenance

The analyticity step follows the countability argument of
Casselman–Shalika (source ID `casselman-shalika-1980-whittaker`), Section 2, Step 2:
for each parameter `u`, some averaging level works; one level works for
uncountably many `u`, and holomorphy then extends it to all `u`. The
lemmas below are the general ingredients of that argument in the form used
by the Lean proof. They are internal content of this proof; the sources do
not state them as numbered results.

## Complex analysis (section `Complex`)

- `exists_accPt_of_not_countable`: an uncountable set `S ⊆ ℂ` has an
  accumulation point. Some closed ball `closedBall 0 n` meets `S` in an
  infinite set (otherwise `S` is a countable union of finite sets), and an
  infinite subset of a compact set has an accumulation point.
- `eq_zero_of_not_countable`: an entire function `f : ℂ → ℂ` whose zero set
  is uncountable vanishes everywhere, by the identity theorem
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`) at an
  accumulation point of the zero set.
- `differentiable_ofReal_cpow`: `u ↦ b^u` is entire for real `b > 0`.
- `sum_cpow_smul_eq_zero_of_not_countable`: in any complex vector space
  `V`, if a finite sum `∑_{i ∈ s} b_i^u • w_i` with real `b_i > 0` vanishes
  for uncountably many `u`, it vanishes for every `u`. Every linear form
  `φ : V → ℂ` turns the sum into an entire function, which vanishes by the
  previous lemma; then `Module.forall_dual_apply_eq_zero_iff`.

## Integrals (section `Integral`)

- `differentiable_setIntegral_mul_cpow μ hK hβ hβpos hα`: for a compact set
  `K` in a Hausdorff space with an opens-measurable measure `μ`, a function
  `α` integrable on `K`, and a locally constant `β > 0`, the function
  `u ↦ ∫_K α(x) β(x)^u dμ` is entire. On `K` the function `β` takes
  finitely many values `b`, the fibres `K ∩ β⁻¹(b)` are measurable and
  disjoint, and the integral equals `∑_b b^u ∫_{K ∩ β⁻¹(b)} α`.

## The upper unipotent group (section `Group`)

`F` is a `p`-adic field with its canonical topology.

- `isOpen_ker_inverseStandardCharacter F ψ n`: the kernel of
  `inverseStandardCharacter ψ n` on `upperUnipotent (n + 1) F` is open. The
  sum of the superdiagonal entries is continuous and `ψ` is trivial near `0`
  (`character_eq_one_mem_nhds`, from the nonvanishing helper module), so the
  kernel is a neighbourhood of `1`, hence an open subgroup.
- `exists_upperUnipotent_exhaustion F n`: there are compact open subgroups
  `S 0 ≤ S 1 ≤ …` of `upperUnipotent n F` whose union is the whole group.
  The group is closed in a σ-compact group, hence σ-compact, and every
  compact subset lies in a compact open subgroup by the published
  `upperUnipotentCompactContainment`; the `S k` are chosen recursively to
  contain the `k`-th compact covering set and `S (k - 1)`.
- `exists_matrix_exhaustion F a b`: there is a sequence of compact sets
  `E R` of `a × b` matrices over `F` such that every compact set lies in
  some `E R` (a compact exhaustion of the locally compact, second countable
  space of matrices).
