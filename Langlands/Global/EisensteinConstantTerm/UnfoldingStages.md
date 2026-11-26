# Integration over a discrete quotient in stages

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingStages`, namespace
`Langlands.Global.LeftCosetSpace`. It proves a Weil-type formula for a discrete subgroup `Δ`
contained in a closed subgroup `H` of a locally compact, second countable, Hausdorff group `G`,
for functions that are only left `Δ`-invariant.

## Setting

`H ≤ G` is closed, `μH` is a left and right invariant, s-finite measure on `H`, finite on
compacts, `μG` is a measure on `G` finite on compacts, and `ν` is a measure on the left
quotient `H \ G` compatible with `(μG, μH)` in the sense of
`Langlands.QuotientIntegration.IsCompatible`. Let `Δ ≤ H` be a subgroup with `Δ ∩ H` countable,
`D ⊆ G` a measurable transversal of the left action of `Δ` (every `g` has a unique `γ ∈ Δ` with
`γ g ∈ D`), and `t ⊆ H` a fundamental domain of `Δ` in `H` for `μH`.

## Results

- `lintegral_orbitKernel_indicator`, `integral_orbitKernel_indicator`: on the orbit `H g`, the
  integral of `1_D f` against the orbit kernel `orbitKernel H hH μH` equals
  `∫_{a ∈ t} f(a g) dμH(a)`, for `f` measurable and left `Δ`-invariant. The set of `a ∈ H` with
  `a g ∈ D` is a fundamental domain of `Δ` in `H` (`isFundamentalDomain_subgroupSlice`), and
  integrals of invariant functions over two fundamental domains agree.
- `lintegral_transversal_eq` (nonnegative form): for measurable left `Δ`-invariant
  `f : G → ℝ≥0∞`, `∫⁻_{x ∈ D} f x dμG = ∫⁻_q ∫⁻_{a ∈ t} f(a · q̄) dμH dν(q)`, where `q̄ = Quotient.out q`.
  The proof combines the previous item with the Library's `lintegral_orbitKernel`.
- `integral_transversal_eq` (Bochner form): if `f`, with values in a real normed space, is
  strongly measurable, left `Δ`-invariant and integrable on `D`, then
  `q ↦ ∫_{a ∈ t} f(a · q̄) dμH` is `ν`-integrable and
  `∫_{x ∈ D} f x dμG = ∫_q ∫_{a ∈ t} f(a · q̄) dμH dν(q)`. The proof uses
  `orbitKernel_comp` (the composite of the orbit kernel with `ν` is `μG`) and Mathlib's
  `ProbabilityTheory.Kernel.integral_comp`.

## Provenance

These are the "integration in stages" identities
`∫_{Δ \ G} f = ∫_{H \ G} ∫_{Δ \ H} f(h g) dh dg` (Weil's formula for `Δ ≤ H ≤ G`), stated with
fundamental domains and the Library's compatible quotient measures. They are derived from the
Library's orbit-kernel form of the compatibility condition.
