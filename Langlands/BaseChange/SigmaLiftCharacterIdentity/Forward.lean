import Langlands.BaseChange.ConcordantIntegralEqualityStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.LocalValues
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Localization
import Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularOpen
import Langlands.BaseChange.SigmaLiftCharacterIdentityStatement
import Langlands.LinearAlgebra.MatrixSquarefreeCharpolyConjugacy

/-! # From the distributional σ-lift identity to the Shintani identity -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis
open ConcordanceLocalization SigmaLiftCharacterIdentity

namespace SigmaLiftCharacterIdentity

private lemma characteristic_integral_ne_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {K : Set X} (hK : IsClopen K) (hcK : IsCompact K)
    (hne : K.Nonempty) : (∫ x, Hecke.TestFunction.characteristic hK hcK x ∂μ) ≠ 0 := by
  change (∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂μ) ≠ 0
  rw [integral_indicator_const _ hK.isClosed.measurableSet, Measure.real]
  simpa using Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos
    (hK.isOpen.measure_pos μ hne).ne' hcK.measure_lt_top.ne).ne'

end SigmaLiftCharacterIdentity

/-- Conditional forward direction of Henniart–Lemaire II.2.9, with the local
character, transfer, integration, and regular-locus inputs named explicitly. -/
def SigmaLiftCharacterIdentityForwardStatement.{u, v, uV, uW} : Prop :=
  TwistedCharacterRegularValuesStatement.{u, u, uV} →
  TwistedCharacterRegularValuesStatement.{u, v, uW} →
  RegularTransferStatement.{u, v} →
  ConcordantIntegralEqualityStatement.{u, v} →
  SigmaRegularOpenStatement.{u, v} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (c : ℂ),
        IsSigmaLift σ l π hπ τ hτ A c → IsShintaniLift σ l π hπ τ hτ A c

theorem sigmaLiftCharacterIdentityForward.{u, v, uV, uW} :
    SigmaLiftCharacterIdentityForwardStatement.{u, v, uV, uW} := by
  classical
  intro hregularF hregularE htransfer hintegrals hopen F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ hπirr hτirr A c hsigma
  refine ⟨hsigma.1, ?_⟩
  intro δ γ hassoc hγ
  have hδ : IsSigmaRegular σ l δ := ⟨γ, hassoc, hγ⟩
  obtain ⟨a, ha⟩ := ordinary_regular_values F n hregularF π hπ hπirr γ hγ
  obtain ⟨b, hb⟩ := hregularE F E σ l n hE τ hτ hτirr A δ hδ
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let μF : Measure (GeneralLinear n F) := Measure.haar
  let μE : Measure (GeneralLinear n E) := Measure.haar
  have : μF.IsHaarMeasure := by dsimp [μF]; infer_instance
  have : μE.IsHaarMeasure := by dsimp [μE]; infer_instance
  obtain ⟨U, hU, hγU, hvalF⟩ := ha μF
  obtain ⟨Wδ, hWδ, hδW, hvalE⟩ := hb μE
  obtain ⟨K, hcK, hK, hδK, hKsub⟩ :=
    exists_isCompact_isClopen_subset (hWδ.inter (hopen F E σ l n hE)) ⟨hδW, hδ⟩
  let φ := Hecke.TestFunction.characteristic hK hcK
  have hφ : IsSigmaRegularSupported σ l φ := by
    change Function.support (φ : GeneralLinear n E → ℂ) ⊆ {d | IsSigmaRegular σ l d}
    rw [Hecke.TestFunction.support_characteristic]
    exact hKsub.trans Set.inter_subset_right
  obtain ⟨f, -, hmatch⟩ := (htransfer F E σ l n hE μF μE).1 φ hφ
  let qE (d : GeneralLinear n E) := coefficients (cyclicNorm σ l d)
  let qF (g : GeneralLinear n F) := coefficients (baseChange F E n g)
  have hqE : Continuous qE := continuous_coefficients.comp (continuous_cyclicNorm σ l)
  have hqF : Continuous qF := continuous_coefficients.comp continuous_baseChange
  have := finiteAlgebra_t2Space F E
  have := finiteAlgebra_locallyCompactSpace F E
  have := finiteAlgebra_totallyDisconnectedSpace F E
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  obtain ⟨B, hB, hγB, hfU⟩ := exists_cutoff_support hqF f (isOpen_conjugacySaturation hU)
    (y := qF γ) (by
      intro g _ hg
      have hpoly := charpoly_eq_of_baseChange_coefficients hE hg
      obtain ⟨x, hx⟩ := matrixConj_of_squarefree_charpoly_eq
        (γ : Matrix (Fin n) (Fin n) F) (g : Matrix (Fin n) (Fin n) F) hsep.squarefree hpoly.symm
      have hconj : x * γ * x⁻¹ = g := Units.ext hx
      rw [← hconj]
      exact conj_mem_conjugacySaturation hγU x)
  let φB := cutoff (hB.preimage hqE) φ
  let fB := cutoff (hB.preimage hqF) f
  have hmatchB : AreConcordant σ l μF μE φB fB :=
    concordant_cutoff hmatch hqE hqF (coefficients_cyclicNorm_conj hE.pow_eq_one)
      coefficients_baseChange_conj (fun _ _ h => coefficients_associated h) hB
  have hφBW : Function.support φB ⊆ Wδ := by
    change Function.support (cutoff (hB.preimage hqE) φ) ⊆ Wδ
    rw [support_cutoff, Hecke.TestFunction.support_characteristic]
    exact Set.inter_subset_left.trans (hKsub.trans Set.inter_subset_left)
  have hnonzero : (∫ d, φB d ∂μE) ≠ 0 := by
    change (∫ d, cutoff (hB.preimage hqE) (Hecke.TestFunction.characteristic hK hcK) d ∂μE) ≠ 0
    rw [cutoff_characteristic]
    refine characteristic_integral_ne_zero μE _ _ ⟨δ, hδK, ?_⟩
    change coefficients (cyclicNorm σ l δ) ∈ B
    rw [coefficients_associated hassoc]
    exact hγB
  have h := hsigma.2 μF μE φB fB hmatchB
  have hmass := hintegrals F E σ l n hE μF μE φB fB hmatchB
  rw [hvalE φB hφBW, evaluate_saturation hU hvalF fB hfU, ← hmass, ← mul_assoc] at h
  have hab : b = c * a := mul_right_cancel₀ hnonzero h
  exact ⟨a, ha, hab ▸ hb⟩

end Langlands.BaseChange
