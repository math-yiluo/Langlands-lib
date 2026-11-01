# Analytic consequences of a scaled kernel tower

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis`,
namespace `Langlands.RankinSelberg.TwoBlockUnipotentQuotient`.

Author: Worker 235.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`
(JPSS 1983, Section 4.6, printed pages 411-412). It derives the analytic
conclusions of that statement for one restricted pair of quotient measures:
the nonnegative Tonelli identity, the characterization of absolute
integrability, and the integrability and Bochner formula for the published
`radicalAverage`. The hypotheses are a kernel `κ` from `N \ GL_(t+1)` to
`H \ GL_(t+1)` with the radical fiber law and a scaled identity
`κ ∘ₘ ν_N = c • ν_H` with `0 < c < ∞`. The module does not construct `κ`, the
quotient measures or the identity `κ ∘ₘ ν_N = c • ν_H`. Those are separate
parts of the proof.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
411-412, integrate a function on `H \ GL_(t+1)` by first integrating over the
fibres `x ↦ [u(x) g]_H` and then over `N \ GL_(t+1)`. The source uses Fubini
for this decomposition without stating it separately. The kernel formulation
and the lemmas below are internal content of this proof. The objects
`LeftUnipotentQuotient`, `BlockQuotient`, `fiberPoint` and `radicalAverage` are
the published ones of
`Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`, and the
measurable structures are those of the target statement (Borel σ-algebras on
both quotients).

## Generic scaled kernel towers (section `Generic`)

Let `κ` be a kernel from `X` to `Y`, `ν` a measure on `X`, `μ` a measure on `Y`
and `c : ℝ≥0∞`, with `κ ∘ₘ ν = c • μ`.

- `lintegral_lintegral_of_comp_eq_smul`: for measurable `f : Y → ℝ≥0∞`,
  `∫⁻ q, ∫⁻ z, f z ∂κ q ∂ν = c * ∫⁻ z, f z ∂μ`. This is
  `Measure.lintegral_bind` applied to `κ ∘ₘ ν`.
- `integrable_iff_of_comp_eq_smul`: if `c ≠ 0` and `c ≠ ∞`, then an a.e.
  strongly measurable `f : Y → E` is `μ`-integrable exactly when
  `f` is `κ q`-integrable for `ν`-almost every `q` and `q ↦ ∫ z, ‖f z‖ ∂κ q` is
  `ν`-integrable. Integrability against `μ` and against `c • μ` agree
  (`integrable_smul_measure`), and the latter is Mathlib's
  `Measure.integrable_comp_iff`.
- `integral_integral_of_comp_eq_smul`: if `c ≠ ∞` and `f` is `μ`-integrable
  (values in a real normed space), then `q ↦ ∫ z, f z ∂κ q` is `ν`-integrable and
  `∫ q, ∫ z, f z ∂κ q ∂ν = c.toReal • ∫ z, f z ∂μ`. The proof writes
  `κ ∘ₘ ν` as the composition of kernels from the one-point space and applies
  `Integrable.integral_comp`, `Kernel.integral_comp` and `integral_smul_measure`.

## The radical average as a kernel integral

- `radicalAverage_eq_integral_kernel`: in the setting of the target statement,
  let `μR` be an additive Haar measure on `R = M((m 0 + 1) × (m 1 + 1))` and let
  `κ` be a kernel with `κ [g]_N = map (fun x => fiberPoint h F x g) μR` for every
  `g`. Then for every measurable `f : H \ GL_(t+1) → ℂ`,
  `radicalAverage F h μR f = fun q => ∫ z, f z ∂κ q`. On a representative `g` the
  published `radicalAverage_mk` gives `∫ x, f [u(x) g]_H ∂μR`. The fiber map
  `x ↦ [u(x) g]_H` is continuous, so `integral_map` turns this into the
  integral against `κ [g]_N`.

## The analytic conjuncts

- `analytic_of_comp_eq_smul`: in the setting of the target statement, let `μR`
  be an additive Haar measure, `c ≠ 0`, `c ≠ ⊤`, and `κ` an s-finite kernel with
  the radical fiber law above. Let `νNs` be an s-finite measure on
  `N \ GL_(t+1)` and `νHs` a measure on `H \ GL_(t+1)` with
  `κ ∘ₘ νNs = c • νHs`. Then three conclusions hold:
  1. `∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs = c * ∫⁻ z, f z ∂νHs` for measurable
     nonnegative `f`;
  2. for measurable `f : H \ GL_(t+1) → ℂ`, `f` is `νHs`-integrable exactly
     when it is `κ q`-integrable for `νNs`-almost every `q` and
     `q ↦ ∫ z, ‖f z‖ ∂κ q` is `νNs`-integrable;
  3. if such an `f` is `νHs`-integrable, then `radicalAverage F h μR f` is
     `νNs`-integrable and
     `∫ q, radicalAverage F h μR f q ∂νNs = c.toReal • ∫ z, f z ∂νHs`.

  These are exactly the Tonelli, integrability and Bochner conjuncts of the
  target statement for the pair `νNs = ν_N|_s`, `νHs = ν_H|_(π⁻¹ s)`. The
  proof applies the three generic lemmas, and for item 3 it first rewrites
  `radicalAverage` by `radicalAverage_eq_integral_kernel`. The two measures
  are arbitrary here; the restriction and the compatibility of the quotient
  measures do not enter.
