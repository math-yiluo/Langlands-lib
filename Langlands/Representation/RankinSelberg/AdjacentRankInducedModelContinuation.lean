import Langlands.Representation.RankinSelberg.AdjacentRankMatrixWitnesses
import Langlands.Representation.RankinSelberg.AdjacentRankModelImageProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.Induction.OppositeProductReversalProof

/-! Actual normalized lower induction in the large-second-twist product formulas. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance inducedModelTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance inducedModelValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance inducedModelLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance inducedModelFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance inducedModelFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance inducedModelFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance inducedModelFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance inducedModelGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance inducedModelGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance inducedModelUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance inducedModelUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance inducedModelQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance inducedModelQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

private theorem normalizedProductWhittakerType_of_sizes
    (ψ : UnitaryAdditiveCharacter F.Carrier) (t : ℕ)
    (B : BlockShape (t + 1)) (m : Fin B.length → ℕ)
    (hsize : ∀ i, B.size i = m i + 1)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (hsize i ▸ σ i)) :
    IsOfWhittakerType t (standardCharacter ψ t)
      (F.canonicalNormalizedProductInduced B σ) := by
  cases B with
  | mk k size hpos hsum =>
    dsimp only at m hsize V σ hσ ⊢
    have hs : size = fun i => m i + 1 := funext hsize
    subst size
    exact normalizedProductWhittakerType p F ψ t k m hsum σ hσ

/-- The actual normalized lower induction has full Whittaker type. The proof
uses the canonical normalized conjugation and reverses the complete block
family, including the dependent original carriers and their representations. -/
theorem adjacentRankNormalizedOpposite_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (χ : Quasicharacter F.Carrier) :
    IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1))
      (F.canonicalNormalizedOppositeParabolicInduced
        (Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0))
        ((Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))) := by
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let C := Shahidi.pairCarrier V (ULift.{uV} ℂ)
  let ρ := Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)
  have hsmooth : ∀ i, IsSmooth (ρ i) := by
    intro i
    fin_cases i
    · exact hσ.1.1
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  obtain ⟨E, -, -⟩ := glOppositeProductReversal p F
    F.canonicalTopologicalData (r + 2) B C ρ hsmooth
  let : ∀ i : Fin B.reverse.length, AddCommGroup (C i.rev) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (C i.rev) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  let ρrev : ∀ i : Fin B.reverse.length,
      Representation ℂ (GeneralLinear (B.reverse.size i) F.Carrier) (C i.rev) :=
    fun i => ρ i.rev
  let m : Fin B.reverse.length → ℕ := ![0, r]
  have hsize : ∀ i, B.reverse.size i = m i + 1 := by
    intro i
    fin_cases i <;> rfl
  have hblocks : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (hsize i ▸ ρrev i) := by
    intro i
    fin_cases i
    · exact rankOneExtensionCharacter_isOfWhittakerType F ψ χ
    · exact hσ
  have hupper := normalizedProductWhittakerType_of_sizes F ψ (r + 1)
    B.reverse m hsize ρrev hblocks
  exact hupper.of_equiv E.symm

/-- A bound chosen from the published whole-function image theorem. It
precedes the real second twist and every separated model test/vector. -/
def adjacentRankInducedModelBound
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ₀ : Quasicharacter F.Carrier) : ℝ :=
  (adjacentRankModelImage p F ψ μ hself r V σ hσ ℓ hℓ χ₀).choose

/-- Above the model-image bound, one actual nonzero induced functional
realizes every separated test/vector and supplies both matched rational
product formulas without analytic or matrix-witness premises. -/
theorem adjacentRankNormalizedOpposite_matchedProductContinuation
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ₀ : Quasicharacter F.Carrier)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (u : ℝ) (hu : adjacentRankInducedModelBound F ψ μ hself σ hσ ℓ hℓ χ₀ < u) :
    let χ := AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
    let B₀ := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
    let π := F.canonicalNormalizedOppositeParabolicInduced B₀
      (B₀.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
    ∃ ℓU : glFunctionals ψ (r + 1) π, ℓU.val ≠ 0 ∧
      ∀ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
        (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier)),
        IsRowFourierPair ψ μ φ φHat →
        ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule,
          (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
            (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) ∧
          let ΦD := adjacentRankReflectedTest
            (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
          let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
            (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
          let UD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback π)
            (dualFunctional ψ π ℓU) (dualModelLinearMap ψ π ℓU U)
          ∃ (N : ℕ)
            (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
            ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
              ∃ (f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
                (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
                (glModelRepresentation (ψ.scale (-1)) r τ ℓ'))
                (M MD : Fin N → RationalFunctions),
                (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
                  (generalLinearHaar F.Carrier r) Φ
                  (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i)) ∧
                (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
                  (generalLinearHaar F.Carrier r) ΦD
                  (fun h => (χ⁻¹ (determinant h) : ℂ) *
                    GodementJacquet.coefficientIota (f i).val h) (MD i)) ∧
                AdjacentRankProductContinuationData F ψ ν W.val
                  (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
                  U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
                  Φ φ χ (fun i => (f i).val) M 1 ∧
                AdjacentRankProductContinuationData F (ψ.scale (-1)) ν WD.val
                  (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
                  UD.val (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
                  ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
                  MD (adjacentRankModelStarScalar F χ r) := by
  let χ := AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
  let B₀ := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let π := F.canonicalNormalizedOppositeParabolicInduced B₀
    (B₀.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
  have hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π :=
    adjacentRankNormalizedOpposite_isOfWhittakerType F ψ σ hσ χ
  obtain ⟨ℓU, hℓU, himage⟩ :=
    (adjacentRankModelImage p F ψ μ hself r V σ hσ ℓ hℓ χ₀).choose_spec u hu
  refine ⟨ℓU, hℓU, fun Φ φ φHat hφ W => ?_⟩
  let Ψ := adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W
  have hmem : (fun g => adjacentRankModelIntegral F ψ μ hself σ ℓ χ Ψ g) ∈
      Set.range (fun v : π.asModule => fun g => ℓU.val (π g v)) := by
    exact himage.le ⟨Ψ, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  let U := modelMap π ℓU v
  have hU : ∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ Ψ g :=
    fun g => congrFun hv g
  exact ⟨U, hU, adjacentRankModel_matchedProductContinuation_exists F ψ μ hself
    σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ ℓU hℓU U hU τ hτ ℓ' hℓ' ν hν⟩

end Langlands.RankinSelberg.Padic
