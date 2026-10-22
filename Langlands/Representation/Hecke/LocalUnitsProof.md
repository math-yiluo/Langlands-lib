# Finite-family compact-open local units

`Langlands.Hecke.HeckeAlgebra.finiteFamilyLocalUnits.{u}` proves exactly the
published proposition `FiniteFamilyLocalUnitsStatement.{u}`. For any
Hausdorff locally compact totally disconnected topological group `G : Type u`,
compatible Borel measurable structure, left Haar measure `μ`, finite family
`s : Finset (HeckeAlgebra μ)`, and open subgroup `U`, it supplies a compact
open subgroup `K ≤ U`. The normalized indicator
`e_K = (μ.real (K : Set G) : ℂ)⁻¹ • 1_K` satisfies
`e_K * e_K = e_K` and `e_K * f = f = f * e_K` for every `f ∈ s`.
Here multiplication is the published left-Haar convolution
`(f * g)(x) = ∫ y, f(y) * g(y⁻¹ * x) ∂μ`.

The proof first applies `TestFunction.commonCompactOpenBiInvariance` to
`G`, `s`, and `U`. The carrier `HeckeAlgebra μ` is definitionally
`Langlands.HarmonicAnalysis.SchwartzBruhat G`, so this gives the required
subgroup, compactness, and bi-invariance for the original family directly.
The theorem `normalizedIndicator_idempotent` provides idempotence.
For each family member, the two components of its bi-invariance give the
hypotheses of `normalizedIndicator_mul_of_leftInvariant` and
`mul_normalizedIndicator_of_rightInvariant`, respectively. These yield the
left and right convolution-unit identities.

The proof also covers the empty finite family: the common-invariance theorem
still supplies a compact open subgroup inside `U`, and the idempotence
theorem applies to its normalized indicator. It retains the arbitrary
universe and all hypotheses of the fixed statement. It requires no
countability, sigma-finiteness, unimodularity, subgroup normality, or
additional compact-open-basis assumption.

This is an internal derivation from the published modules
`LocalUnitsStatement`, `CommonInvarianceProof`, and `NormalizedIndicator`,
rather than a separately quoted original-source theorem. The proof uses
their actual function carrier, normalized indicator, and convolution.

Worker 86 authored the proof draft and its initial explanation. Worker 108
prepared this proof contribution and expanded the paired explanation.
