import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationReductionProof
import Langlands.AllField.Representation.Classification.IrreducibleProductEmbedding
import Langlands.AllField.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationProof
import Langlands.AllField.Representation.GodementJacquet.GenericMatrixFunctionalEquationReductionStatement
import Langlands.AllField.Representation.GodementJacquet.SubquotientFunctionalEquationDescent
/-! Conditional irreducible reduction from the two full analytic bases. -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement GenericMatrixFunctionalEquationReductionStatement GenericMatrixFunctionalEquationStatement MatrixUnitValueStatement SupercuspidalMatrixFunctionalEquationStatement TateMatrixFunctionalEquationStatement TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion finiteProductMatrixFunctionalEquation genericMatrixFunctionalEquationReduction inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff matrixUnitValue padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatchedZetaExpansion twoBlockMatrixAnalyticInduction twoBlockMatrixAnalyticInduction_of_ordinary twoBlockMatrixFunctionalEquationInduction twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockOrdinaryMatrixAnalyticInduction
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

namespace Padic
open Langlands.GodementJacquet.Padic hiding HasNormalizedMatrixFunctionalEquationData IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData SubquotientCoefficientInclusionStatement aestronglyMeasurable_dualParabolicIntegrand dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel exists_biSmoothCoefficient_ne_zero exists_matrixIntegral_one finiteProductMeasurable finiteProductProofBorel finiteProductProofDisconnected finiteProductProofGLBorel finiteProductProofGLMeasurable finiteProductProofLocalField finiteProductProofMeasurable finiteProductProofT2 finiteProductProofTopology finiteProductProofValuation finiteProductTopology generalLinearHaar_measurePreserving_inverseTranspose genericMatrixReductionBorel genericMatrixReductionDisconnected genericMatrixReductionLocalField genericMatrixReductionMeasurable genericMatrixReductionT2 genericMatrixReductionTopology genericMatrixReductionValuation hasNormalizedMatrixFunctionalEquationData_equiv instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft iotaMatrixAnalyticAssertions_succBlocks_iff iotaMatrixRationalValues jpssI2 jpssI3 map_mulLeftMeasurableEquiv matrixAnalyticAssertions_reversedInverseTransposeBlocks matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation measurable_inverseTranspose_val mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply normalizedMatrixFunctionalEquationData_of_coefficient_inclusion normalizedMatrixFunctionalEquationData_of_subquotient one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem subquotientCoefficientInclusion subquotientDescentBorelSpace subquotientDescentGLBorelSpace subquotientDescentGLMeasurableSpace subquotientDescentLocalField subquotientDescentMeasurableSpace subquotientDescentT2Space subquotientDescentTopology subquotientDescentTotallyDisconnectedSpace subquotientDescentValuativeRel twoBlockReversalGLBorel twoBlockReversalGLMeasurable twoBlockReversalLocalField twoBlockReversalTopology twoBlockReversalValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement GenericMatrixFunctionalEquationReductionStatement GenericMatrixFunctionalEquationStatement IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData SubquotientCoefficientInclusionStatement SupercuspidalMatrixFunctionalEquationStatement TateMatrixFunctionalEquationStatement TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement TwoBlockOrdinaryMatrixAnalyticInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion finiteProductMatrixFunctionalEquation genericMatrixFunctionalEquationReduction inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant subquotientCoefficientInclusion twoBlockMatchedZetaExpansion twoBlockMatrixAnalyticInduction twoBlockMatrixAnalyticInduction_of_ordinary twoBlockMatrixFunctionalEquationInduction twoBlockMatrixFunctionalEquationInduction_of_expansion twoBlockOrdinaryMatrixAnalyticInduction whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance genericMatrixReductionMeasurable : MeasurableSpace F := borel _
local instance genericMatrixReductionBorel : BorelSpace F := ⟨rfl⟩
local instance genericMatrixReductionT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance genericMatrixReductionDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- Restrict the actual smooth Schur character to scalar matrices. -/
private theorem exists_scalarQuasicharacter {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    ∃ ω : Quasicharacter F,
      Classification.HasGLCentralCharacter F r σ ω.toMonoidHom := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup r
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter σ ha hi
  let ω : Quasicharacter F :=
    ⟨χ.comp GeneralLinear.scalarToCenter,
      hlc.continuous.comp (GeneralLinear.scalarContinuous.continuous.subtype_mk _)⟩
  exact ⟨ω, fun a v => hact (GeneralLinear.scalarToCenter a) v⟩

/-- Apply the rank-one or higher-rank supercuspidal analytic base. -/
private theorem hasData_supercuspidal
    (hTate : TateMatrixFunctionalEquationStatement.{uF,uV})
    (hSuper : SupercuspidalMatrixFunctionalEquationStatement.{uF,uV})
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    {r : ℕ} (hr : 0 < r)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F) V)
    (hσ : IsSupercuspidal σ) (hi : σ.IsIrreducible) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ := by
  cases r with
  | zero => omega
  | succ s =>
    cases s with
    | zero => exact hTate F ψ ν hsd V σ hσ.1 hi
    | succ t =>
      obtain ⟨c, a, h⟩ := hSuper F ψ ν hsd t V σ hσ hi
      exact ⟨1, 1, c, a, h⟩

/-- A genuine injection exhibits the source as an actual subquotient. -/
private theorem hasData_of_injective {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (j : σ.IntertwiningMap τ) (hj : Function.Injective j) (hτ : IsSmooth τ)
    (hdata : HasNormalizedMatrixFunctionalEquationData F ψ ν τ) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ := by
  let jR : σ.IntertwiningMap j.range.toRepresentation :=
    { toLinearMap := j.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun f : V →ₗ[ℂ] W => f v) (j.isIntertwining' g) }
  have hbij : Function.Bijective jR := by
    constructor
    · intro v w h
      exact hj (congrArg Subtype.val h)
    · rintro ⟨w, v, rfl⟩
      exact ⟨v, rfl⟩
  let e := jR.ofBijective hbij
  obtain ⟨P, PDual, c, a, h⟩ := hdata
  exact normalizedMatrixFunctionalEquationData_of_subquotient F ψ ν hsd hτ
    j.range e.symm.toIntertwiningMap e.symm.surjective h

end Padic

/-- Reduce the unchanged generic statement to the two unchanged analytic bases. -/
theorem genericMatrixFunctionalEquationReduction :
    GenericMatrixFunctionalEquationReductionStatement.{uF,uV} := by
  intro hTate hSuper F _ _ _ _ ψ ν hsd n V _ _ σ hσ hi
  classical
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  let : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)) σ.asModule
  let A : SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (n + 1) F) :=
    SmoothRep.of σ hσ.1.1
  obtain ⟨B, C, j, hj⟩ :=
    Langlands.AllField.Classification.irreducible_supercuspidalProduct_embedding.{uF,uV,uV}
      F (⟨⟩ : LocalFieldData F) (n + 1) (Nat.succ_pos n) A hi
  choose ω hω using fun i =>
    Langlands.AllField.GodementJacquet.Padic.exists_scalarQuasicharacter F (C i).obj.representation
      (C i).property.2.1 (C i).property.1
  have hC : ∀ i, Langlands.AllField.GodementJacquet.Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
      (C i).obj.representation := fun i =>
    Langlands.AllField.GodementJacquet.Padic.hasData_supercuspidal F hTate hSuper ψ ν hsd
      (B.positive i) (C i).obj.representation (C i).property.2 (C i).property.1
  have hprod := finiteProductMatrixFunctionalEquation F (n + 1)
    (Nat.succ_pos n) B (fun i => (C i).obj) (fun i => (C i).property.2.1)
    ψ ν hsd ω hω hC
  have hsmooth : IsSmooth
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (C i).obj.representation)) :=
    (((⟨⟩ : LocalFieldData F).normalizedProductInductionFunctor B).obj
      (fun i => (C i).obj)).isSmooth
  exact Langlands.AllField.GodementJacquet.Padic.hasData_of_injective F ψ ν hsd j hj hsmooth hprod

end Langlands.AllField.GodementJacquet
