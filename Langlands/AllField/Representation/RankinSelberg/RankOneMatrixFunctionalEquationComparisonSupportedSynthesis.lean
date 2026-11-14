import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSupportedSynthesis
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
/-! Supported matrix synthesis and genuine weighted integral expansion. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding compactMatrixLift compactMatrixLift_orbit compactMatrixLift_support exists_supported_compactMatrixLift supportedSynthesisLocalField supportedSynthesisNBorel supportedSynthesisNMeasurable supportedSynthesisT2 supportedSynthesisTopology supportedSynthesisValuativeRel
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker

universe uK uF

section General


end General

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance supportedSynthesisT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance supportedSynthesisNMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance supportedSynthesisNBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- Every actual compact standard-character induced function has a supported
matrix lift with absolutely convergent orbit integrals at every point. -/
theorem exists_supported_compactMatrixLift
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    ∃ Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
      tsupport (Φ : _ → ℂ) ⊆
        Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F) ∧
      (∀ g : Langlands.GeneralLinear (n + 1) F,
        Integrable (fun u : upperUnipotent (n + 1) F =>
          (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val)
          (unipotentHaar F n)) ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        (∫ u : upperUnipotent (n + 1) F,
          (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val
            ∂unipotentHaar F n) = eval _ _ f.val g := by
  have hbasis : ∀ O : Set (Langlands.GeneralLinear (n + 1) F), IsOpen O →
      (1 : Langlands.GeneralLinear (n + 1) F) ∈ O →
      ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)) ∧
          (L : Set (Langlands.GeneralLinear (n + 1) F)) ⊆ O := by
    intro O hO h1
    exact ⟨((⟨⟩ : LocalFieldData F).generalLinearCompactOpen (n + 1) O
      (hO.mem_nhds h1)).val,
      ((⟨⟩ : LocalFieldData F).generalLinearCompactOpen (n + 1) O
        (hO.mem_nhds h1)).property⟩
  exact exists_supported_matrix_characterOrbitIntegral_eq (n + 1) hbasis
    (upperUnipotent (n + 1) F) UpperUnipotent.isClosed
    (unipotentHaar F n) (standardCharacter ψ n)
    (standardCharacterContinuous ψ n).continuous f

/-- A fixed supported matrix lift; it is independent of the second matrix
test and the determinant-weight parameter. -/
def compactMatrixLift (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  Classical.choose (exists_supported_compactMatrixLift F ψ n f)

theorem compactMatrixLift_support (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n))) :
    tsupport (compactMatrixLift F ψ n f : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  (Classical.choose_spec (exists_supported_compactMatrixLift F ψ n f)).1

theorem compactMatrixLift_orbit (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (∫ u : upperUnipotent (n + 1) F,
      (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val
        ∂unipotentHaar F n) = eval _ _ f.val g :=
  (Classical.choose_spec (exists_supported_compactMatrixLift F ψ n f)).2.2 g

end CanonicalPadic

end Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
