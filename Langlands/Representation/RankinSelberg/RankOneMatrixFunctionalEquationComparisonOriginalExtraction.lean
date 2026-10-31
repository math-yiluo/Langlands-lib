import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOriginalBlockZero

/-! # Original matrix-to-block extraction with the actual averaged coefficient

The positive box factor and all choices of box and averaging subgroup remain
available for the simultaneous Fourier comparison.
-/

noncomputable section

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance originalExtractionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance originalExtractionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance originalExtractionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance originalExtractionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance originalExtractionScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance originalExtractionScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance originalExtractionGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance originalExtractionGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance originalExtractionUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance originalExtractionUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance originalExtractionQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance originalExtractionQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))

/-- The original scalar comparison for a specified actual matrix coefficient,
test and scalar, against the literal block-zero integral. -/
def OriginalMatrixBlockComparison
    (Φ : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) (C : ℂ) : Prop :=
  ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    GodementJacquet.matrixIntegral (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier (m + 1)) Φ
        (s + GodementJacquet.jpssShift (m + 1)) f.val =
      C * unequalRankIntegralAt 0 ((m + 1) - 0 - 1) (by omega) ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (rectangularMeasure ν 0 (0 + 1)) w.val (rankOneTrivialModelOne ψ).val s

/-- Any actual coefficient agreeing with the model function on the specified
box has the original comparison, with a positive real scalar independent of `s`. -/
theorem originalMatrixBlockComparison_of_eq_on_box
    (hσ : IsSmooth σ)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    {A q : ℤ} {a : ℕ} (hbox : ModelBoxConditions F ψ σ ℓ w A q a)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (heq : ∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
      g.val ∈ box F A q a → f.val g = glModelFunction ψ (m + 1) σ ℓ w g) :
    ∃ C : ℝ, 0 < C ∧
      OriginalMatrixBlockComparison F ψ ν σ ℓ w μ
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
          (isOpen_box F A q a)) f (C : ℂ) := by
  obtain ⟨C, hC, hcomp⟩ := box_comparison_of_integrable F ψ σ ℓ w hσ hbox
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨C, hC, b, fun s hs => ?_⟩
  have hm := hb (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
    (isOpen_box F A q a)) f s hs
  change Integrable _ _ at hm
  have he := box_matrixIntegrand_eq_of_eq_on_box F heq
    (s + GodementJacquet.jpssShift (m + 1))
  rw [he] at hm
  rw [unequalRankIntegralAt_rankOne_one ψ _ ν σ ℓ w μ hμ]
  change (∫ g, GodementJacquet.matrixIntegrand _ _ _ f.val g ∂_) = _
  rw [he]
  exact (hcomp s hm).2

/-- The original extraction retains the actual box, compact averaging subgroup,
test invariance and pointwise coefficient equality, together with its positive
comparison scalar. No additional rank-one analytic premise is used. -/
theorem exists_originalMatrixBlockComparison
    (hσ : IsSmooth σ)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ (A q : ℤ) (a : ℕ), ModelBoxConditions F ψ σ ℓ w A q a ∧
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier),
        ∃ hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)),
          (∀ k ∈ K,
            (∀ M, (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) (k.val * M) =
              (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) M) ∧
              normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1) ∧
          (∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
            g.val ∈ box F A q a →
              (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
                glModelFunction ψ (m + 1) σ ℓ w g) ∧
          ∃ C : ℝ, 0 < C ∧
            OriginalMatrixBlockComparison F ψ ν σ ℓ w μ
              (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a))
              (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w)
              (C : ℂ) := by
  obtain ⟨A, q, a, hbox, K, hK, hInv, heq⟩ :=
    exists_box_averagedModelCoefficient_eq F ψ σ ℓ w hσ
  refine ⟨A, q, a, hbox, K, hK, hInv, heq, ?_⟩
  exact originalMatrixBlockComparison_of_eq_on_box F ψ ν σ ℓ w μ hσ hμ hMatrix hbox
    (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w) heq

end Langlands.RankinSelberg.RankOneBox
