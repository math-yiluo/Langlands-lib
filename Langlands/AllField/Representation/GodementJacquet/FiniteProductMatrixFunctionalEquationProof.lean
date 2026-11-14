import Langlands.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationProof
import Langlands.AllField.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.AllField.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof
import Langlands.AllField.Representation.Parabolic.HeadTailProductInduction
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
/-! Finite products, by actual singleton evaluation and first/tail induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion finiteProductMatrixFunctionalEquation inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatchedZetaExpansion twoBlockMatrixAnalyticInduction twoBlockMatrixAnalyticInduction_of_ordinary twoBlockMatrixFunctionalEquationInduction twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockOrdinaryMatrixAnalyticInduction
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

namespace Padic
open Langlands.GodementJacquet.Padic hiding HasNormalizedMatrixFunctionalEquationData IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData aestronglyMeasurable_dualParabolicIntegrand dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel finiteProductMeasurable finiteProductProofBorel finiteProductProofDisconnected finiteProductProofGLBorel finiteProductProofGLMeasurable finiteProductProofLocalField finiteProductProofMeasurable finiteProductProofT2 finiteProductProofTopology finiteProductProofValuation finiteProductTopology generalLinearHaar_measurePreserving_inverseTranspose hasNormalizedMatrixFunctionalEquationData_equiv instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft iotaMatrixAnalyticAssertions_succBlocks_iff iotaMatrixRationalValues jpssI2 jpssI3 map_mulLeftMeasurableEquiv matrixAnalyticAssertions_reversedInverseTransposeBlocks matrixIntegral matrixIntegrand matrixRationalValues measurable_inverseTranspose_val mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem twoBlockReversalGLBorel twoBlockReversalGLMeasurable twoBlockReversalLocalField twoBlockReversalTopology twoBlockReversalValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion finiteProductMatrixFunctionalEquation inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatchedZetaExpansion twoBlockMatrixAnalyticInduction twoBlockMatrixAnalyticInduction_of_ordinary twoBlockMatrixFunctionalEquationInduction twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockOrdinaryMatrixAnalyticInduction whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance finiteProductProofMeasurable : MeasurableSpace F := borel _
local instance finiteProductProofBorel : BorelSpace F := ⟨rfl⟩
local instance finiteProductProofT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance finiteProductProofDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance finiteProductProofGLMeasurable (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear r F) := borel _
local instance finiteProductProofGLBorel (r : ℕ) : BorelSpace (Langlands.GeneralLinear r F) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)

/-- Existence of the full data transports across an actual equivalence. -/
theorem hasNormalizedMatrixFunctionalEquationData_equiv {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Langlands.GeneralLinear r F) V}
    {τ : Representation ℂ (Langlands.GeneralLinear r F) W}
    (e : σ.Equiv τ) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ ↔
      HasNormalizedMatrixFunctionalEquationData F ψ ν τ := by
  cases r with
  | zero => rfl
  | succ n =>
    change (∃ P PDual c a, NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a) ↔
      ∃ P PDual c a, NormalizedMatrixFunctionalEquationData F ψ ν τ P PDual c a
    constructor
    · rintro ⟨P, PDual, c, a, h⟩
      exact ⟨P, PDual, c, a, (GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
        (q := (⟨⟩ : LocalFieldData F).residueCardinality) (ψ := ψ) (ν := ν)
        (abv := Langlands.AllField.RankinSelberg.normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (μ := RankinSelberg.generalLinearHaar F n) e).mp h⟩
    · rintro ⟨P, PDual, c, a, h⟩
      exact ⟨P, PDual, c, a, (GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
        (q := (⟨⟩ : LocalFieldData F).residueCardinality) (ψ := ψ) (ν := ν)
        (abv := Langlands.AllField.RankinSelberg.normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (μ := RankinSelberg.generalLinearHaar F n) e).mpr h⟩

/-- Singleton closure uses the actual single-block evaluation equivalence. -/
private theorem hasData_singleton {r : ℕ} (B : BlockShape r) (hl : B.length = 1)
    (A : ∀ i, SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F))
    (hA : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (A i).representation)) := by
  rcases B with ⟨l, s, hp, hs⟩
  dsimp at hl
  subst l
  have hsize : s = fun _ : Fin 1 => r := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa using hs
  subst s
  let B : BlockShape r := ⟨1, fun _ => r, hp, hs⟩
  have hf : (fun i => ((B.singleBlock_size rfl i).symm ▸ A 0 :
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F))) = A := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have e := (⟨⟩ : LocalFieldData F).singleBlockTransportedProductEquiv B rfl (A 0)
  let D := fun AA : ∀ i, SmoothRep.{0,uF,uV} ℂ
    (Langlands.GeneralLinear (B.size i) F) =>
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (AA i).representation))
  have hD : D (fun i => ((B.singleBlock_size rfl i).symm ▸ A 0 :
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F))) :=
    (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν e).mpr (hA 0)
  exact Eq.mp (congrArg D hf) hD

/-- Apply the published successor-rank two-block theorem to an arbitrary
actual two-block shape, using only equality of its ordered positive sizes. -/
private theorem hasData_twoBlock {r : ℕ} (hr : 0 < r) (B : BlockShape r)
    (hl : B.length = 2)
    (A : ∀ i, SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F))
    (hadm : ∀ i, IsAdmissible (A i).representation)
    (hsd : IsSelfDual ψ ν) (ω : Fin B.length → Quasicharacter F)
    (hω : ∀ i, Classification.HasGLCentralCharacter F (B.size i)
      (A i).representation (ω i).toMonoidHom)
    (hA : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (A i).representation)) := by
  classical
  cases r with
  | zero => omega
  | succ t =>
    rcases B with ⟨l, s, hp, hs⟩
    dsimp at hl
    subst l
    obtain ⟨m, rfl⟩ : ∃ m : Fin 2 → ℕ, s = fun i => m i + 1 := by
      refine ⟨fun i => s i - 1, funext fun i => ?_⟩
      have := hp i
      dsimp
      omega
    change ∀ i, ∃ P PDual c a,
      NormalizedMatrixFunctionalEquationData F ψ ν (A i).representation P PDual c a at hA
    choose P PDual c a hdata using hA
    exact ⟨_, _, _, _, twoBlockMatrixFunctionalEquationInduction F t m hs
      (fun i => A i) (fun i => (A i).representation) (fun i => (A i).isSmooth)
      hadm ψ ν hsd ω hω P PDual c a hdata⟩

/-- Induction on the nonempty ordered block family. The tail uses the
original carrier universe; only the outer pair is lifted. -/
private theorem hasData_finite (hsd : IsSelfDual ψ ν) (k : ℕ) :
    ∀ (r : ℕ), 0 < r → ∀ (B : BlockShape r), B.length = k + 1 →
    ∀ (A : ∀ i, SmoothRep.{0,uF,uV} ℂ
      (Langlands.GeneralLinear (B.size i) F)),
    (∀ i, IsAdmissible (A i).representation) →
    ∀ (ω : Fin B.length → Quasicharacter F),
    (∀ i, Classification.HasGLCentralCharacter F (B.size i)
      (A i).representation (ω i).toMonoidHom) →
    (∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) →
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (A i).representation)) := by
  classical
  induction k with
  | zero =>
    intro r _ B hl A _ _ _ hA
    exact hasData_singleton F ψ ν B hl A hA
  | succ k ih =>
    intro r hr B hl A hadm ω hω hA
    let T := (⟨⟩ : LocalFieldData F)
    let tail : SmoothRep.{0,uF,max uF uV} ℂ
        (Langlands.GeneralLinear (B.tailRank hl) F) :=
      (T.normalizedProductInductionFunctor (B.tailShape hl)).obj
        (fun j => A (B.tailIndex hl j))
    have htail : HasNormalizedMatrixFunctionalEquationData F ψ ν tail.representation :=
      ih (B.tailRank hl) (B.tailRank_pos hl) (B.tailShape hl) rfl
        (fun j => A (B.tailIndex hl j)) (fun j => hadm (B.tailIndex hl j))
        (fun j => ω (B.tailIndex hl j)) (fun j => hω (B.tailIndex hl j))
        (fun j => hA (B.tailIndex hl j))
    have hadmtail : IsAdmissible tail.representation :=
      Langlands.AllField.Parabolic.normalizedInductionAdmissibility F T (B.tailShape hl) _
        ((B.tailShape hl).blockTensor (fun j => (A (B.tailIndex hl j)).representation))
        (FiniteTensor.isAdmissible_external _ (fun j => hadm (B.tailIndex hl j)))
    let ωtail : Quasicharacter F := ∏ j, ω (B.tailIndex hl j)
    have hcharstail : ωtail.toMonoidHom =
        ∏ j, (ω (B.tailIndex hl j)).toMonoidHom := by
      ext a
      simp [ωtail]
      let ev : Quasicharacter F →* ℂˣ :=
        { toFun := fun χ => χ a
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have heval : (∏ j, ω (B.tailIndex hl j)) a =
          ∏ j, (ω (B.tailIndex hl j)) a := map_prod ev _ _
      rw [heval]
      simp
    have hωtail : Classification.HasGLCentralCharacter F (B.tailRank hl)
        tail.representation ωtail.toMonoidHom := by
      rw [hcharstail]
      exact T.hasScalarCharacter_normalizedProductInduced (B.tailShape hl)
        (fun j => hω (B.tailIndex hl j))
    let C := T.headTailProductFactors B hl A
    let ωC : Fin 2 → Quasicharacter F :=
      Fin.cases (ω (B.headIndex hl)) (fun _ => ωtail)
    have hadmC : ∀ i, IsAdmissible (C i).representation := by
      intro i
      fin_cases i
      · exact (SmoothRep.isAdmissible_universeLift_iff (A (B.headIndex hl))).mpr
          (hadm (B.headIndex hl))
      · exact hadmtail
    have hωC : ∀ i, Classification.HasGLCentralCharacter F
        ((B.headTailShape hl).size i) (C i).representation (ωC i).toMonoidHom := by
      intro i
      fin_cases i
      · intro a v
        change ULift.up ((A (B.headIndex hl)).representation (GeneralLinear.scalar a)
          v.down) = ULift.up _
        rw [hω (B.headIndex hl) a v.down]
        rfl
      · exact hωtail
    have hC : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (C i).representation := by
      intro i
      fin_cases i
      · exact (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν
          (SmoothRep.universeLiftEquiv.{uF} (A (B.headIndex hl)))).mp (hA (B.headIndex hl))
      · exact htail
    have houter := hasData_twoBlock F ψ ν hr (B.headTailShape hl) rfl C hadmC hsd ωC hωC hC
    exact (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν
      (T.headTailProductInductionEquiv B hl A)).mpr houter

end Padic

/-- Full data exist on the actual finite normalized product if they exist on
its smooth admissible factors with supplied scalar central quasicharacters. -/
theorem finiteProductMatrixFunctionalEquation :
    FiniteProductMatrixFunctionalEquationStatement.{uF,uV} := by
  intro F _ _ _ _ r hr B A hadm ψ ν hsd ω hω hA
  have hl : B.length ≠ 0 := by
    intro hz
    have hsum : (∑ i, B.size i) = 0 := Finset.sum_eq_zero fun i _ => by
      have := i.isLt
      omega
    have := B.sum_eq
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl
  exact Langlands.AllField.GodementJacquet.Padic.hasData_finite F ψ ν hsd k r hr B hk A hadm ω hω hA

end Langlands.AllField.GodementJacquet
