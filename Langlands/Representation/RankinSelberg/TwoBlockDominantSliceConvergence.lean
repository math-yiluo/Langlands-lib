import Langlands.Representation.RankinSelberg.TwoBlockDominantNormEnvelope
import Langlands.Representation.RankinSelberg.QuotientTorusEnvelope
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof

/-! # Genuine slice convergence of the actual dominant kernel -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockDeformation TwoBlockJacquet TwoBlockConvergence TwoBlockLowerFixedSlice
  TwoBlockLowerUnipotentQuotient
open scoped BigOperators NNReal ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance sliceConvergenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance sliceConvergenceValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance sliceConvergenceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance sliceConvergenceT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance sliceConvergenceSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance sliceConvergenceMeasurable : MeasurableSpace F.Carrier := borel _
local instance sliceConvergenceBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance sliceConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance sliceConvergenceGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance sliceConvergenceNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance sliceConvergenceNBorel (n : ℕ) :
    BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance sliceConvergenceQMeasurable (t : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
local instance sliceConvergenceQBorel (t : ℕ) :
    BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
local instance sliceConvergenceLowerMeasurable {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance sliceConvergenceLowerBorel {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every actual standard quotient point has a torus times integral
representative; this is an existence argument, not a chosen section. -/
theorem exists_standard_torus_representative (q : LeftUnipotentQuotient t F.Carrier) :
    ∃ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier),
      c ∈ integralOpen F t ∧ q = Quotient.mk _ (Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨v, hv, lam, c, hc, rfl⟩ :=
      Iwasawa.exists_iwasawa (uniformizerUnit_isUniformizingElement F) g
    refine ⟨lam, c, (mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc), ?_⟩
    rw [mul_assoc]
    exact leftQuotientMap_subgroup_mul _ ⟨v, hv⟩ _

/-- One threshold before all complementary dimensions gives a summable
majorant for the actual integrated raw norm and complex average. -/
theorem exists_summable_kernelNorm_majorant
    (ν : AdditiveHaarMeasure F.Carrier) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ C : ℝ, ∀ (u : ℝ), C < u →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (j k : ℕ) (hr : r = t + (j + k + 1))
        (Wtest : (coefficientModel π lambda).toSubmodule),
      ∃ A : (Fin (t + 1) → ℤ) → ℝ,
        (∀ lam, 0 ≤ A lam) ∧
        Summable (fun lam => diagonalDensity F lam * A lam) ∧
        ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier),
          c ∈ integralOpen F t →
          let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
          let z := (lowerToStandard h F.Carrier).symm (Quotient.mk _
            (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
              F.canonicalTopologicalData) lam * c))
          let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
          quotientFiberIntegrable ν ellu f Wtest.val hr s0 z ∧
          ‖quotientKernel ν ellu f Wtest.val hr s0 z‖ ≤ A lam ∧
          ‖quotientNormProfile ν ellu f Wtest.val hr s0 z‖ ≤ A lam := by
  classical
  obtain ⟨B, hB, hbound⟩ :=
    exists_kernelNorm_torus_envelope ν h ψ π hπ lambda τ hτ ell a ha
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  let D : ℝ := q ^ (2 * (t + 1) * (t + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨C, _, hC⟩ := exists_geometric_twist_threshold (B := D * B) hq
  refine ⟨C, fun u hu f j k hr Wtest => ?_⟩
  obtain ⟨hu0, hratio⟩ := hC u hu
  obtain ⟨K, M, hK0, hK⟩ := hbound u f j k hr Wtest
  refine ⟨coneMajorant (Finset.Iic a.castSucc) K B q u M,
    coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le), ?_, ?_⟩
  · apply Summable.of_nonneg_of_le
      (fun lam => mul_nonneg (diagonalDensity_nonneg F lam)
        (coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le) lam)) _
      ((summable_cone_twist (M := M) (Finset.Iic a.castSucc) hq
        (mul_nonneg (zero_le_one.trans hD) hB0) hu0 hratio).mul_left K)
    intro lam
    unfold coneMajorant
    split_ifs with hc
    · calc
        _ ≤ D ^ torusSize lam * (K * B ^ torusSize lam *
            q ^ (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) :=
          mul_le_mul_of_nonneg_right (diagonalDensity_le F lam) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · simp
  · intro lam c hc
    dsimp only
    rw [lowerToStandard_symm_mk]
    have henv := hK lam c hc
    dsimp only at henv
    simp only [mul_assoc] at henv
    obtain ⟨hi, hn, hp0, hp, hs⟩ := henv
    change FiberIntegrable _ _ _ _ _ _ _ ∧
      ‖representativeKernel _ _ _ _ _ _ _‖ ≤ _ ∧
      ‖representativeNormProfile _ _ _ _ _ _ _‖ ≤ _
    refine ⟨hi, ?_⟩
    have hprofile : representativeNormProfile ν
        (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val hr
        (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ))
        ((blockRotation h F.Carrier)⁻¹ *
          (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
            F.canonicalTopologicalData) lam * c)) ≤
          coneMajorant (Finset.Iic a.castSucc) K B q u M lam := by
      unfold coneMajorant
      split_ifs with hcone
      · simpa only [mul_assoc] using hp
      · have hz : representativeNormProfile ν
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val hr
            (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ))
            ((blockRotation h F.Carrier)⁻¹ *
              (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
                F.canonicalTopologicalData) lam * c)) = 0 := by
          by_contra hne
          exact hcone (hs (by simpa only [mul_assoc] using hne))
        rw [hz]
    constructor
    · exact hn.trans hprofile
    · rw [Real.norm_eq_abs, abs_of_nonneg (by simpa only [mul_assoc] using hp0)]
      exact hprofile

/-- A measurable actual kernel and raw-norm profile with one summable torus
bound give genuine absolute input for the exact supplied quotient measure.
The fiber assertion is extended to every quotient point by Iwasawa coverage. -/
theorem kernelAbsoluteIntegrable_of_summable_torus_bound
    {j k : ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : AdditiveHaarMeasure F.Carrier)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hνN : standardCompatible F hN νN)
    (A : (Fin (t + 1) → ℤ) → ℝ)
    (hsum : Summable (fun lam => diagonalDensity F lam * A lam))
    (hbound : ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier),
      c ∈ integralOpen F t →
      let z := (lowerToStandard h F.Carrier).symm (Quotient.mk _
        (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
          F.canonicalTopologicalData) lam * c))
      quotientFiberIntegrable ν ell f Wtest.val hr s z ∧
      ‖quotientKernel ν ell f Wtest.val hr s z‖ ≤ A lam ∧
      ‖quotientNormProfile ν ell f Wtest.val hr s z‖ ≤ A lam) :
    KernelAbsoluteIntegrable ν ell f Wtest.val hr s νN ∧
      ∀ z, quotientFiberIntegrable ν ell f Wtest.val hr s z := by
  let := hN
  let E : LeftUnipotentQuotient t F.Carrier → ℂ := fun q =>
    quotientKernel ν ell f Wtest.val hr s ((lowerToStandard h F.Carrier).symm q)
  let P : LeftUnipotentQuotient t F.Carrier → ℝ := fun q =>
    quotientNormProfile ν ell f Wtest.val hr s ((lowerToStandard h F.Carrier).symm q)
  have hE : Measurable E :=
    (measurable_quotientKernel ν ell f π hπ lambda Wtest hr s).comp
      (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  have hP : Measurable P :=
    (measurable_quotientNormProfile ν ell f π hπ lambda Wtest hr s).comp
      (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  have hEi : Integrable E νN := by
    apply QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F F.canonicalTopologicalData t νN hνN
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      (uniformizerUnit_isUniformizingElement F) E hE A _ hsum
    intro lam c hc
    exact (hbound lam c ((mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc))).2.1
  have hPiC : Integrable (fun q => (P q : ℂ)) νN := by
    apply QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F F.canonicalTopologicalData t νN hνN
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      (uniformizerUnit_isUniformizingElement F) _ (Complex.measurable_ofReal.comp hP)
      A _ hsum
    intro lam c hc
    change ‖(P (Quotient.mk _ (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c)) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact (hbound lam c ((mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc))).2.2
  have hPi : Integrable P νN := by
    change Integrable (fun q => (P q : ℂ).re) νN
    exact hPiC.re
  have hfiber : ∀ z, quotientFiberIntegrable ν ell f Wtest.val hr s z := by
    intro z
    obtain ⟨lam, c, hc, heq⟩ :=
      exists_standard_torus_representative ((lowerToStandard h F.Carrier) z)
    have hz : z = (lowerToStandard h F.Carrier).symm (Quotient.mk _
        (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit
          F.canonicalTopologicalData) lam * c)) := by
      apply (lowerToStandard h F.Carrier).injective
      simpa only [Equiv.apply_symm_apply] using heq
    rw [hz]
    exact (hbound lam c hc).1
  refine ⟨(kernelAbsoluteIntegrable_standard_iff ν ell f Wtest.val hr s νN).mpr
    ⟨hEi, hPi, Filter.Eventually.of_forall (fun q => hfiber _)⟩, hfiber⟩

/-- Restricting the supplied standard measure restricts all three actual
absolute-input conditions to the corresponding lower determinant slice. -/
theorem kernelAbsoluteIntegrable_restrict
    {j k : ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : AdditiveHaarMeasure F.Carrier)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hi : KernelAbsoluteIntegrable ν ell f Wtest hr s νN) (d : ℤ) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) := by
  rcases hi with ⟨hK, hP, hf⟩
  change Integrable _ _ ∧ Integrable _ _ ∧ _
  have hm : lowerMeasure F h
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) =
      (lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    (lowerMeasure_restrict F h νN d).symm
  rw [hm]
  exact ⟨hK.restrict, hP.restrict, ae_restrict_of_ae hf⟩

/-- One bound precedes the twist, every supplied compatible measure, both
rectangle dimensions and all tests. Convergence on each determinant slice
holds for every spectral parameter, independently of any epsilon equation. -/
def IsUniformSliceConvergence
    (ν : AdditiveHaarMeasure F.Carrier) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
      (νN : Measure (LeftUnipotentQuotient t F.Carrier)),
      standardCompatible F hN νN →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (j k : ℕ) (hr : r = t + (j + k + 1))
        (Wtest : (coefficientModel π lambda).toSubmodule),
        let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
        (∀ s : ℂ, Measurable (quotientKernel ν ellu f Wtest.val hr s) ∧
          Measurable (quotientNormProfile ν ellu f Wtest.val hr s)) ∧
        (∀ (s : ℂ) z, quotientFiberIntegrable ν ellu f Wtest.val hr s z) ∧
        ∀ (s : ℂ) (d : ℤ), KernelAbsoluteIntegrable ν ellu f Wtest.val hr s
          (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d))

/-- The actual raw-norm envelope and quotient integration prove the uniform
slice convergence package for full Whittaker-type representations. -/
theorem exists_uniform_slice_convergence
    (ν : AdditiveHaarMeasure F.Carrier) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ C : ℝ, IsUniformSliceConvergence ν h ψ π lambda τ ell C := by
  have hlt : m 1 < t := by
    have hh : m 0 + 1 + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    omega
  let a : Fin t := ⟨m 1, hlt⟩
  obtain ⟨C, hC⟩ :=
    exists_summable_kernelNorm_majorant ν h ψ π hπ lambda τ hτ ell a rfl
  refine ⟨C, fun u hu hN νN hνN f j k hr Wtest => ?_⟩
  dsimp only
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
  obtain ⟨A, _, hsum, hb⟩ := hC u hu f j k hr Wtest
  obtain ⟨hi, hf⟩ := kernelAbsoluteIntegrable_of_summable_torus_bound
    ν ellu f π hπ.1.1 lambda Wtest hr s0 hN νN hνN A hsum hb
  have hf0 (z : LowerQuotient h F.Carrier) :
      quotientFiberIntegrable ν ellu f Wtest.val hr 0 z :=
    (quotientFiberIntegrable_spectral_iff ν ellu f Wtest.val hr s0 z).mp (hf z)
  refine ⟨fun s => ⟨measurable_quotientKernel ν ellu f π hπ.1.1 lambda Wtest hr s,
    measurable_quotientNormProfile ν ellu f π hπ.1.1 lambda Wtest hr s⟩,
    fun s z => (quotientFiberIntegrable_spectral_iff ν ellu f Wtest.val hr s z).mpr (hf0 z),
    fun s d => ?_⟩
  have hi0 := (kernelAbsoluteIntegrable_restrict_spectral_iff
    ν ellu f Wtest.val νN hr s0 d).mp
      (kernelAbsoluteIntegrable_restrict ν ellu f Wtest.val hr s0 νN hi d)
  exact (kernelAbsoluteIntegrable_restrict_spectral_iff
    ν ellu f Wtest.val νN hr s d).mpr hi0

end Langlands.RankinSelberg.TwoBlockDominantRectangular
