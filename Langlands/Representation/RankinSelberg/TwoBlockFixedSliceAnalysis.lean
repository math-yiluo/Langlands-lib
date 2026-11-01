import Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Continuity of the actual first-unfolding averages

Internal analytic helpers for the fixed-slice unfolding of JPSS Section 4.6.
The open right stabilizer of a smooth section makes its entire raw Jacquet
integrand, as a function of the rectangular variable, locally constant in the
group variable. Integrating therefore preserves local constancy without a
parameter-dependent domination argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockUnfolding

open GeneralLinear TwoBlockJacquet TwoBlockUnipotentQuotient QuotientIntegration
  Whittaker HarmonicAnalysis MeasureTheory

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}

section Raw

variable (ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier) (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- The whole rectangular integrand is locally constant in the group argument. -/
theorem rawIntegrand_isLocallyConstant (f : Sections F h σ) :
    letI := F.canonicalTopologicalData.topology
    IsLocallyConstant (fun g => TwoBlockJacquet.integrand ψ ell f g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun a => g⁻¹ * a) ⁻¹' (K : Set (GeneralLinear (t + 1) F.Carrier)),
    K.isOpen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro a ha
  funext x
  have hfix := congrArg
    (fun v => v.val (upperRadical h F.Carrier x * g)) (hK ⟨g⁻¹ * a, ha⟩)
  change f.val.val ((upperRadical h F.Carrier x * g) * (g⁻¹ * a)) =
    f.val.val (upperRadical h F.Carrier x * g) at hfix
  have heval : sectionEval F h σ f (upperRadical h F.Carrier x * a) =
      sectionEval F h σ f (upperRadical h F.Carrier x * g) := by
    simpa only [sectionEval, Induction.eval, mul_assoc, mul_inv_cancel_left] using hfix
  simp only [TwoBlockJacquet.integrand_apply, heval]

/-- The actual raw Jacquet family, bundled as a locally constant map into
functions on the rectangular radical. -/
def rawIntegrandLocallyConstant (f : Sections F h σ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    LocallyConstant (GeneralLinear (t + 1) F.Carrier)
      (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier → ℂ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact ⟨fun g => TwoBlockJacquet.integrand ψ ell f g,
    rawIntegrand_isLocallyConstant ψ ell f⟩

end Raw

section Averages

variable (ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier)
variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : letI := F.canonicalTopologicalData.topology
  WhittakerFunctions ψ t)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

/-- Continuity descends from the actual continuous group integrand. -/
theorem integrand_continuous :
    letI := F.canonicalTopologicalData.topology
    Continuous Wtest.val → Continuous (integrand ell f Wtest Φ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro hW
  have hs : Continuous (fun g => scalarSection (fun i => (ell i).val) f g 1) := by
    simpa only [scalarSection_one, Function.comp_def] using
      ((Induction.eval_isLocallyConstant _ _ f).comp (tensorContraction (fun i => (ell i).val))).continuous
  have hr : Continuous (lastRow : GeneralLinear (t + 1) F.Carrier → _) :=
    continuous_pi (fun j => Units.continuous_val.matrix_elem (Fin.last t) j)
  apply (leftQuotient_isOpenQuotientMap (blockUnipotent h F.Carrier)).isQuotientMap.continuous_iff.mpr
  exact (hW.mul hs).mul (Φ.locallyConstant.continuous.comp hr)

variable [MeasurableSpace F.Carrier]

/-- Absolute fiber average on a representative, factored into row norms and
an integral of the absolute raw Jacquet integrand. -/
theorem radicalAverage_norm_integrand_mk :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μR.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F.Carrier),
      radicalAverage F h μR (fun z => (‖integrand ell f Wtest Φ z‖ : ℂ)) (Quotient.mk _ g) =
        (‖Wtest.val g‖ : ℂ) *
          (∫ x, (‖TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) *
          (‖Φ (lastRow g)‖ : ℂ) := by
  let := F.canonicalTopologicalData.topology
  intro _ μR _ g
  simp only [radicalAverage_mk, integrand_fiberPoint, norm_mul, Complex.ofReal_mul,
    integral_mul_const, integral_const_mul]

/-- Both the signed and absolute averages are continuous. No convergence
hypothesis is used here; convergence will be supplied separately. -/
theorem radicalAverages_continuous :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μR.IsAddHaarMeasure], Continuous Wtest.val →
      Continuous (radicalAverage F h μR (integrand ell f Wtest Φ)) ∧
      Continuous (radicalAverage F h μR (fun z => (‖integrand ell f Wtest Φ z‖ : ℂ))) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro _ μR _ hW
  have hlc := rawIntegrand_isLocallyConstant ψ (fun i => (ell i).val) f
  have hj : Continuous (jacquetFunction ψ (fun i => (ell i).val) μR f) :=
    (hlc.comp (fun v => ∫ x, v x ∂μR)).continuous
  have ha : Continuous (fun g => ∫ x,
      (‖TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) :=
    (hlc.comp (fun v => ∫ x, (‖v x‖ : ℂ) ∂μR)).continuous
  have hr : Continuous (fun g : GeneralLinear (t + 1) F.Carrier => Φ (lastRow g)) :=
    Φ.locallyConstant.continuous.comp
      (continuous_pi (fun j => Units.continuous_val.matrix_elem (Fin.last t) j))
  constructor
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Pi.mul_def, leftQuotientMap_apply, radicalAverage_integrand_mk] using
      (hW.mul hj).mul hr
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Pi.mul_def, leftQuotientMap_apply, radicalAverage_norm_integrand_mk] using
      ((Complex.continuous_ofReal.comp hW.norm).mul ha).mul
        (Complex.continuous_ofReal.comp hr.norm)

end Averages

end Langlands.RankinSelberg.TwoBlockUnfolding
