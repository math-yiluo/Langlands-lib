import Langlands.Representation.RankinSelberg.AdjacentRankCompactCoefficients
import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral

/-! The same compact-average family after Weyl/inverse-transpose transformation. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualCompactFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualCompactValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualCompactLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualCompactGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualCompactGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

/-- The normalized middle compact average of the actual Weyl/inverse-transpose
transform of a group function, for the unchanged canonical group Haar. -/
def adjacentRankDualMiddleAverage {r : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F.Carrier))
    (W : GeneralLinear (r + 1) F.Carrier → ℂ)
    (g h : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  ((generalLinearHaar F.Carrier r).real (K : Set _) : ℂ)⁻¹ *
    ∫ k in (K : Set _), dualFunction r W (g * k * h) ∂generalLinearHaar F.Carrier r

/-- An inverse-transpose invariant subgroup permits the exact change of
variable in the compact average, without a Haar comparison scalar. -/
theorem adjacentRankDualMiddleAverage_eq {r : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F.Carrier))
    (hK : ∀ k ∈ K, inverseTranspose (r + 1) F.Carrier k ∈ K)
    (W : GeneralLinear (r + 1) F.Carrier → ℂ)
    (g h : GeneralLinear (r + 1) F.Carrier) :
    adjacentRankDualMiddleAverage F K W g h =
      ((generalLinearHaar F.Carrier r).real (K : Set _) : ℂ)⁻¹ *
        ∫ k in (K : Set _),
          W (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier g *
            k * inverseTranspose (r + 1) F.Carrier h) ∂generalLinearHaar F.Carrier r := by
  have hpre : (inverseTranspose (r + 1) F.Carrier) ⁻¹' (K : Set _) = K := by
    ext k
    change inverseTranspose (r + 1) F.Carrier k ∈ K ↔ k ∈ K
    constructor
    · intro hk
      have hh := hK _ hk
      rw [inverseTranspose_involutive] at hh
      exact hh
    · exact hK k
  have hmp := GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F r
  have hemb := (GodementJacquet.inverseTransposeMeasurableEquiv hmp.measurable).measurableEmbedding
  have hi := hmp.setIntegral_preimage_emb hemb
    (fun k => W (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier g *
      k * inverseTranspose (r + 1) F.Carrier h)) (K : Set _)
  rw [hpre] at hi
  unfold adjacentRankDualMiddleAverage
  congr 1
  calc
    (∫ k in (K : Set _), dualFunction r W (g * k * h) ∂generalLinearHaar F.Carrier r) =
        ∫ k in (K : Set _),
          W (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier g *
            inverseTranspose (r + 1) F.Carrier k *
            inverseTranspose (r + 1) F.Carrier h) ∂generalLinearHaar F.Carrier r := by
      apply integral_congr_ae
      filter_upwards [] with k
      change W (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier (g * k * h)) = _
      simp only [map_mul, mul_assoc]
    _ = _ := hi

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- One finite family and its actual bi-smooth matrix coefficients separate
both the original and transformed middle averages. The transformed matrix
functions are precisely inverse-transpose precompositions of the original ones. -/
theorem adjacentRankCompact_middleAverage_and_dual
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (K : OpenSubgroup (GeneralLinear (r + 1) F.Carrier))
    (hKc : IsCompact (K : Set (GeneralLinear (r + 1) F.Carrier)))
    (hKι : ∀ k ∈ K, inverseTranspose (r + 1) F.Carrier k ∈ K) :
    ∃ (N : ℕ) (B : Fin N → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          (∀ g h : GeneralLinear (r + 1) F.Carrier,
            ((generalLinearHaar F.Carrier r).real (K : Set _) : ℂ)⁻¹ *
                (∫ k in (K : Set _), W.val.val (g * k * h)
                  ∂generalLinearHaar F.Carrier r) =
              ∑ i, (B i).val.val g * (f i).val h) ∧
          ∀ g h : GeneralLinear (r + 1) F.Carrier,
            adjacentRankDualMiddleAverage F K W.val.val g h =
              ∑ i, (dualModelLinearMap ψ σ ℓ (B i)).val.val g *
                GodementJacquet.coefficientIota (f i).val h := by
  obtain ⟨N, B, hB⟩ := adjacentRankCompact_middleAverage F ψ σ hσ ℓ K hKc
  refine ⟨N, B, fun W => ?_⟩
  obtain ⟨f, hf⟩ := hB W
  refine ⟨f, hf, fun g h => ?_⟩
  rw [adjacentRankDualMiddleAverage_eq F K hKι]
  exact hf (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier g)
    (inverseTranspose (r + 1) F.Carrier h)

end Langlands.RankinSelberg.Padic
