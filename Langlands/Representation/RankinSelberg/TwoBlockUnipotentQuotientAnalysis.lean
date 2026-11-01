import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement

/-!
# Analytic consequences of a scaled kernel tower

Support for the proof of `TwoBlockUnipotentQuotientIntegrationStatement` (JPSS (1983),
Section 4.6, printed pages 411-412). From a measurable s-finite kernel `κ` from
`N \ GL_(t+1)` to `H \ GL_(t+1)` whose value at `[g]_N` is the pushforward of a rectangular
measure along the radical fiber map, and from a scaled identity `κ ∘ₘ ν_N = c • ν_H` with
`0 < c < ∞`, this module derives the nonnegative Tonelli identity, the characterization of
absolute integrability, and the integrability and Bochner formula for the actual
`radicalAverage`. The kernel and the measure identity are hypotheses here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotient

open GeneralLinear QuotientIntegration TwoBlockJacquet

universe uF

/-! ### Scaled kernel towers on arbitrary measurable spaces -/

section Generic

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {κ : Kernel X Y} {ν : Measure X} {μ : Measure Y} {c : ℝ≥0∞}

/-- Nonnegative Tonelli identity for a scaled kernel tower `κ ∘ₘ ν = c • μ`. -/
theorem lintegral_lintegral_of_comp_eq_smul (hκν : κ ∘ₘ ν = c • μ) {f : Y → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ q, ∫⁻ z, f z ∂κ q ∂ν = c * ∫⁻ z, f z ∂μ := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← hκν,
    Measure.lintegral_bind κ.measurable.aemeasurable hf.aemeasurable]

/-- Integrability for a scaled kernel tower with `0 < c < ∞`: a strongly measurable function
is integrable against `μ` iff it is fiberwise integrable almost everywhere and its fiberwise
norm integral is integrable against `ν`. -/
theorem integrable_iff_of_comp_eq_smul (hκν : κ ∘ₘ ν = c • μ) (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {E : Type*} [NormedAddCommGroup E] {f : Y → E} (hf : AEStronglyMeasurable f μ) :
    Integrable f μ ↔
      (∀ᵐ q ∂ν, Integrable f (κ q)) ∧ Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) ν := by
  rw [← integrable_smul_measure hc0 hc, ← hκν]
  exact Measure.integrable_comp_iff (hκν ▸ hf.smul_measure c)

/-- Bochner formula for a scaled kernel tower with `c < ∞`: the fiber integral of a
`μ`-integrable function is `ν`-integrable, and its integral is `c.toReal` times the
integral against `μ`. -/
theorem integral_integral_of_comp_eq_smul (hκν : κ ∘ₘ ν = c • μ) (hc : c ≠ ∞)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Y → E} (hf : Integrable f μ) :
    Integrable (fun q => ∫ z, f z ∂κ q) ν ∧
      ∫ q, ∫ z, f z ∂κ q ∂ν = c.toReal • ∫ z, f z ∂μ := by
  have hf' : Integrable f (κ ∘ₘ ν) := hκν ▸ hf.smul_measure hc
  rw [Measure.comp_eq_comp_const_apply] at hf'
  refine ⟨by simpa using hf'.integral_comp, ?_⟩
  rw [← integral_smul_measure, ← hκν, Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp hf']
  simp

end Generic

/-! ### The radical average as a kernel integral -/

/-- If the kernel value at every `[g]_N` is the pushforward of `μR` along the radical fiber
map `x ↦ [u(x) g]_H`, then the actual radical average of a measurable function is its
kernel integral at every point of `N \ GL_(t+1)`. -/
theorem radicalAverage_eq_integral_kernel :
    ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := F.canonicalTopologicalData
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI : MeasurableSpace F.Carrier := borel F.Carrier
      letI : BorelSpace F.Carrier := ⟨rfl⟩
      let NQ := LeftUnipotentQuotient t F.Carrier
      let HQ := BlockQuotient h F.Carrier
      let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
      letI : MeasurableSpace NQ := borel NQ
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      ∀ (μR : Measure R) [μR.IsAddHaarMeasure] (κ : Kernel NQ HQ),
        (∀ g : GeneralLinear (t + 1) F.Carrier, κ (Quotient.mk _ g) =
          Measure.map (fun x => fiberPoint h F.Carrier x g) μR) →
        ∀ f : HQ → ℂ, Measurable f →
          radicalAverage F h μR f = fun q => ∫ z, f z ∂κ q := by
  intro p _ F t m h T NQ HQ R μR _ κ hκ f hf
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hcont : Continuous (fun x : R => fiberPoint h F.Carrier x g) :=
      continuous_quotient_mk'.comp ((continuous_upperRadical h F.Carrier).mul continuous_const)
    rw [radicalAverage_mk, hκ g,
      integral_map hcont.measurable.aemeasurable hf.aestronglyMeasurable]

/-! ### The analytic conclusions of the two-block tower -/

/-- The analytic conjuncts of `TwoBlockUnipotentQuotientIntegrationStatement`, for one
restricted pair `ν_N|_s`, `ν_H|_(π⁻¹ s)`, from an s-finite kernel with the radical fiber law
and the scaled restricted identity `κ ∘ₘ ν_N|_s = c • ν_H|_(π⁻¹ s)` with `0 < c < ∞`.
The two restricted measures are arbitrary here; `ν_N|_s` is assumed s-finite. -/
theorem analytic_of_comp_eq_smul :
    ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := F.canonicalTopologicalData
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI : MeasurableSpace F.Carrier := borel F.Carrier
      letI : BorelSpace F.Carrier := ⟨rfl⟩
      let NQ := LeftUnipotentQuotient t F.Carrier
      let HQ := BlockQuotient h F.Carrier
      let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
      letI : MeasurableSpace NQ := borel NQ
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      ∀ (μR : Measure R) [μR.IsAddHaarMeasure] (c : ℝ≥0∞), c ≠ 0 → c ≠ ⊤ →
      ∀ (κ : Kernel NQ HQ) [IsSFiniteKernel κ],
        (∀ g : GeneralLinear (t + 1) F.Carrier, κ (Quotient.mk _ g) =
          Measure.map (fun x => fiberPoint h F.Carrier x g) μR) →
      ∀ (νNs : Measure NQ) [SFinite νNs] (νHs : Measure HQ), κ ∘ₘ νNs = c • νHs →
        (∀ f : HQ → ℝ≥0∞, Measurable f →
          (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs) = c * ∫⁻ z, f z ∂νHs) ∧
        (∀ f : HQ → ℂ, Measurable f →
          (Integrable f νHs ↔
            (∀ᵐ q ∂νNs, Integrable f (κ q)) ∧
            Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νNs) ∧
          (Integrable f νHs →
            Integrable (radicalAverage F h μR f) νNs ∧
            (∫ q, radicalAverage F h μR f q ∂νNs) =
              c.toReal • (∫ z, f z ∂νHs))) := by
  intro p _ F t m h T NQ HQ R μR _ c hc0 hc κ _ hκ νNs _ νHs hκν
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  refine ⟨fun f hf => lintegral_lintegral_of_comp_eq_smul hκν hf, fun f hf => ⟨?_, ?_⟩⟩
  · exact integrable_iff_of_comp_eq_smul hκν hc0 hc hf.aestronglyMeasurable
  · intro hfi
    rw [radicalAverage_eq_integral_kernel F h μR κ hκ f hf]
    exact integral_integral_of_comp_eq_smul hκν hc hfi

end Langlands.RankinSelberg.TwoBlockUnipotentQuotient
