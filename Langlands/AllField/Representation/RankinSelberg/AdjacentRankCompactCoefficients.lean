import Langlands.Representation.RankinSelberg.AdjacentRankCompactCoefficients
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelInclusion
/-! Finite coefficient separation of the normalized compact middle average
in JPSS Section 6.3, formula (7). No topology is placed on a module. -/

noncomputable section

namespace Langlands.AllField.Compact
open Langlands.Compact
open Langlands.AllField.Compact

open scoped BigOperators

universe uG uV


end Langlands.AllField.Compact

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding adjacentRankCompact_middleAverage compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open scoped BigOperators

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance compactCoefficientsMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance compactCoefficientsBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩

set_option maxHeartbeats 1000000 in
/-- Exact finite separation of the normalized middle compact average, in the
specified original coefficient model and its actual bi-smooth coefficient module. -/
theorem adjacentRankCompact_middleAverage
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (r + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F))) :
    ∃ (m : ℕ) (B : Fin m → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin m → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          ∀ (g h : Langlands.GeneralLinear (r + 1) F),
            ((generalLinearHaar F r).real (K : Set _) : ℂ)⁻¹ *
                (∫ k in (K : Set _), glModelFunction ψ r σ ℓ W (g * k * h)
                  ∂generalLinearHaar F r) =
              ∑ i : Fin m, glModelFunction ψ r σ ℓ (B i) g * (f i).val h := by
  let hadm : IsAdmissible (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ) :=
    Langlands.AllField.GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ
  obtain ⟨m, B, hB⟩ := Compact.finiteAverageCoefficients
    (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (glModelRepresentation ψ r σ ℓ) hadm K hK
  refine ⟨m, B, fun W => ?_⟩
  obtain ⟨f, hf⟩ := hB W
  refine ⟨f, fun g h => ?_⟩
  let P := Compact.averageToFixed (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (glModelRepresentation ψ r σ ℓ) hadm K hK
  let A := Langlands.AllField.GodementJacquet.Padic.modelPointAverage F ψ σ hσ.1 ℓ K hK g
  let mass : ℂ := (generalLinearHaar F r).real (K : Set _)
  have hA : A (glModelRepresentation ψ r σ ℓ h W) = mass *
      glModelFunction ψ r σ ℓ (P (glModelRepresentation ψ r σ ℓ h W)).val g := by
    calc
      A (glModelRepresentation ψ r σ ℓ h W) =
          A (P (glModelRepresentation ψ r σ ℓ h W)).val := by
        exact (GodementJacquet.apply_averageMap_of_invariant
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ)
          hadm.1 K hK A
          (fun k hk v => Langlands.AllField.GodementJacquet.Padic.modelPointAverage_invariant F ψ σ hσ.1 ℓ
            K hK g hk v) (glModelRepresentation ψ r σ ℓ h W)).symm
      _ = mass * glModelFunction ψ r σ ℓ
          (P (glModelRepresentation ψ r σ ℓ h W)).val g :=
        Langlands.AllField.GodementJacquet.Padic.modelPointAverage_of_mem_fixedVectors F ψ σ hσ.1 ℓ
          K hK g (P (glModelRepresentation ψ r σ ℓ h W)).property
  have hmiddle : (∫ k in (K : Set _), glModelFunction ψ r σ ℓ W (g * k * h)
      ∂generalLinearHaar F r) =
      mass * glModelFunction ψ r σ ℓ
        (P (glModelRepresentation ψ r σ ℓ h W)).val g := by
    simpa only [A, Langlands.AllField.GodementJacquet.Padic.modelPointAverage_apply, glModelFunction_translate,
      mul_assoc] using hA
  rw [hmiddle, ← mul_assoc,
    inv_mul_cancel₀ (Langlands.AllField.GodementJacquet.Padic.measureReal_openSubgroup_ne_zero F K hK), one_mul]
  let ev : (glCoefficientModel ψ r σ ℓ).toSubmodule →ₗ[ℂ] ℂ :=
    { toFun := fun w => glModelFunction ψ r σ ℓ w g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact hf ev h

end Langlands.AllField.RankinSelberg.Padic
