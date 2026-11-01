import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonProductIntegrability
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-! Supported matrix synthesis and genuine weighted integral expansion. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Induction GeneralLinear Whittaker

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]

/-- Matrix synthesis retaining the invertible ambient support of its witness. -/
theorem exists_supported_matrix_characterOrbitIntegral_eq (r : ℕ)
    (hbasis : ∀ O : Set (Langlands.GeneralLinear r K), IsOpen O →
      (1 : Langlands.GeneralLinear r K) ∈ O →
      ∃ L : OpenSubgroup (Langlands.GeneralLinear r K),
        IsCompact (L : Set (Langlands.GeneralLinear r K)) ∧ (L : Set _) ⊆ O)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [IsHaarMeasure μH] [IsMulRightInvariant μH]
    (χ : H →* ℂˣ) (hχ : Continuous χ)
    (f : CompactFunctions H (characterRepresentation χ)) :
    ∃ Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K),
      tsupport (Φ : _ → ℂ) ⊆
        Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K) ∧
      (∀ g : Langlands.GeneralLinear r K,
        Integrable (fun h : H =>
          (((χ h)⁻¹ : ℂˣ) : ℂ) * Φ ((h : Langlands.GeneralLinear r K) * g).val) μH) ∧
      ∀ g : Langlands.GeneralLinear r K,
        (∫ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) *
          Φ ((h : Langlands.GeneralLinear r K) * g).val ∂μH) =
          eval H (characterRepresentation χ) f.val g := by
  obtain ⟨φ, hφ⟩ := exists_characterOrbitIntegral_eq H hH μH χ hχ hbasis f
  refine ⟨groupTestToMatrixTest r φ, tsupport_groupTestToMatrixTest_subset r φ, ?_, ?_⟩
  · intro g
    simpa only [groupTestToMatrixTest_apply] using characterOrbitIntegrable H hH μH χ hχ φ g
  · intro g
    simpa only [groupTestToMatrixTest_apply, characterOrbitIntegral] using hφ g

end General

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supportedSynthesisTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supportedSynthesisValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supportedSynthesisLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supportedSynthesisT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance supportedSynthesisGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance supportedSynthesisGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance supportedSynthesisNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance supportedSynthesisNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance supportedSynthesisGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance supportedSynthesisGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance supportedSynthesisNMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance supportedSynthesisNBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- Every actual compact standard-character induced function has a supported
matrix lift with absolutely convergent orbit integrals at every point. -/
theorem exists_supported_compactMatrixLift
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    ∃ Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier),
      tsupport (Φ : _ → ℂ) ⊆
        Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ∧
      (∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        Integrable (fun u : upperUnipotent (n + 1) F.Carrier =>
          (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val)
          (unipotentHaar F.Carrier n)) ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        (∫ u : upperUnipotent (n + 1) F.Carrier,
          (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val
            ∂unipotentHaar F.Carrier n) = eval _ _ f.val g := by
  have hbasis : ∀ O : Set (Langlands.GeneralLinear (n + 1) F.Carrier), IsOpen O →
      (1 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ O →
      ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
          (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ⊆ O := by
    intro O hO h1
    exact ⟨(F.canonicalTopologicalData.generalLinearCompactOpen (n + 1) O
      (hO.mem_nhds h1)).val,
      (F.canonicalTopologicalData.generalLinearCompactOpen (n + 1) O
        (hO.mem_nhds h1)).property⟩
  exact exists_supported_matrix_characterOrbitIntegral_eq (n + 1) hbasis
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (unipotentHaar F.Carrier n) (standardCharacter ψ n)
    (standardCharacterContinuous ψ n).continuous f

/-- A fixed supported matrix lift; it is independent of the second matrix
test and the determinant-weight parameter. -/
def compactMatrixLift (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  Classical.choose (exists_supported_compactMatrixLift F ψ n f)

theorem compactMatrixLift_support (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    tsupport (compactMatrixLift F ψ n f : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
  (Classical.choose_spec (exists_supported_compactMatrixLift F ψ n f)).1

theorem compactMatrixLift_orbit_integrable (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Integrable (fun u : upperUnipotent (n + 1) F.Carrier =>
      (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val)
      (unipotentHaar F.Carrier n) :=
  (Classical.choose_spec (exists_supported_compactMatrixLift F ψ n f)).2.1 g

theorem compactMatrixLift_orbit (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val
        ∂unipotentHaar F.Carrier n) = eval _ _ f.val g :=
  (Classical.choose_spec (exists_supported_compactMatrixLift F ψ n f)).2.2 g

theorem compactMatrixLift_weighted_orbit (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val *
        Φ g.val * determinantWeight abv g s ∂unipotentHaar F.Carrier n) =
      eval _ _ f.val g * Φ g.val * determinantWeight abv g s := by
  rw [integral_mul_const, integral_mul_const, compactMatrixLift_orbit]

/-- The compact induced function has a genuinely integrable weighted matrix
pairing, derived from the joint product bound rather than an assumed equation. -/
theorem integrable_compact_matrix_pairing (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      eval _ _ f.val g * Φ g.val * determinantWeight abv g s)
      (generalLinearHaar F.Carrier n) := by
  have h := (integrable_unipotent_matrix_product F ψ n
    (compactMatrixLift F ψ n f) (compactMatrixLift_support F ψ n f) Φ s).integral_prod_right
  simpa only [compactMatrixLift_weighted_orbit] using h

/-- Actual weighted pairing expansion using the same fixed lift, test,
parameter, inverse character and two unchanged Haar measures. -/
theorem compact_matrix_pairing_eq_iterated (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n)))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ) :
    (∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      eval _ _ f.val g * Φ g.val * determinantWeight abv g s
        ∂generalLinearHaar F.Carrier n) =
    ∫ u : upperUnipotent (n + 1) F.Carrier,
      ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val *
          Φ g.val * determinantWeight abv g s
        ∂generalLinearHaar F.Carrier n ∂unipotentHaar F.Carrier n := by
  calc
    _ = ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      ∫ u : upperUnipotent (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * compactMatrixLift F ψ n f (u.val * g).val *
          Φ g.val * determinantWeight abv g s
        ∂unipotentHaar F.Carrier n ∂generalLinearHaar F.Carrier n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g =>
        (compactMatrixLift_weighted_orbit F ψ n f Φ s g).symm
    _ = _ := (integral_unipotent_matrix_swap F ψ n
      (compactMatrixLift F ψ n f) (compactMatrixLift_support F ψ n f) Φ s).symm

end CanonicalPadic

end Langlands.RankinSelberg.CompactWhittakerSynthesis
