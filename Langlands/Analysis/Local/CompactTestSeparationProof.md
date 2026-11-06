# Proof of compact continuous test separation

The theorem `Langlands.Analysis.compactTestSeparation.{u}` proves the
unchanged published `Langlands.Analysis.CompactTestSeparationStatement.{u}`.
It applies to every locally compact Hausdorff second-countable Borel
space in arbitrary universe `u`, every measure `μ`, and every specified
locally integrable complex function `F`. It proves absolute integrability
of every conjugated compact continuous test product, together with the
equivalence between almost-everywhere vanishing and vanishing of all
those tested integrals. No regularity, finiteness on compact sets, finite
total measure, group, or smoothness hypothesis is added.

First, `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`,
applied to the continuous conjugate of the test, proves absolute
integrability of each test pairing. Almost-everywhere vanishing then
implies that every tested integral is zero by
`integral_eq_zero_of_ae`.

For the converse, fix an arbitrary compact set `K`. The hypotheses give
the regular and metrizable topology needed to regard `K` as a closed
Gδ set. The pinned theorem
`exists_continuous_one_zero_of_isCompact_of_isGδ`, with the empty set
as its second closed set, supplies a real continuous compact
cutoff `ρ` with values in `[0,1]` and `K = ρ ⁻¹' {1}`. Its positive
powers `g n = ρ^(n+1)` have compact support. Coercing `g n` to a complex
compact continuous test, and using that conjugation fixes real values,
shows `∫ g n • F = 0`.

These integrands have the fixed integrable majorant
`(tsupport ρ).indicator (fun x => ‖F x‖)`. Integrability follows from
the assumed local integrability on that compact set. Powers equal one
on `K` and tend to zero outside `K`, since there `0 ≤ ρ < 1`.
`tendsto_integral_of_dominated_convergence` therefore gives
`∫ x in K, F x = 0`. The Mathlib theorem
`ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'` proves
almost-everywhere vanishing from these compact-set integrals and local
integrability. Second countability and local compactness supply its
sigma-compactness instance. The majorant uses integrability of `F` on a
compact set, rather than finiteness of the measure of that compact set.

The proof preserves the specified function `F` throughout; it
constructs neither an L² representative nor a bounded raw period
operator. Its source motivation and remaining actual-period/smoothness
obligations are recorded in the target Markdown. This is an internal
analytic prerequisite; the normalized quotient period, all-parabolic
cuspidal realization, source smoothness, and spectral conclusions remain
separate obligations. Worker 116 implemented this cutoff-power proof
using the pinned Mathlib APIs. Worker 1580 adopted the Lean proof
unchanged and expanded this explanation for the focused proof task.
