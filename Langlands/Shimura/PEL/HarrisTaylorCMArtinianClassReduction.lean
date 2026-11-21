import Langlands.Shimura.PEL.HarrisTaylorCMArtinianLevel
import Langlands.Shimura.PEL.HarrisTaylorCMArtinianPolarizedLiftingStatement
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange

/-! # Assembling Harris Artinian lifts from normalized polarized actions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

section Pointed

variable {S T : Scheme.{0}} (b : T ⟶ S) (p : S ⟶ Spec (.of F))
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]

local notation "PObjS" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)
local notation "PObjT" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := T)
local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p)
local notation "GoodT" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C (b ≫ p))
local notation "NumS" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
local notation "NumT" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)

/-- Both normalized conditions hold on a positive polarized action that reduces
to the given one by an equivariant rational isometry. -/
def NormalizedPolarizedActionLiftsAlong : Prop :=
  letI := auxiliaryStarRing D C
  ∀ X : PObjT, GoodT X → NumT X →
    ∃ Y : PObjS, GoodS Y ∧ NumS Y ∧
      ∃ e : (RationalAlgebraAction.pullback b).obj Y.actionObj ≅ X.actionObj,
        PositivePolarizedActionIsometricReduction D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality b Y X e

local notation "Lifts" => NormalizedPolarizedActionLiftsAlong D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

variable {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ Y : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality b Y)
  (lieS : LieBaseChangeNaturalityStatement S)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "mkS" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieS addS addT
local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- An action lift and surjectivity on pointed monodromy lift actual normalized
classes with their levels. -/
theorem classBaseChange_surjective_of_normalizedPolarizedActionLifts
    (hLift : Lifts b p)
    (hα : Function.Surjective (fundamentalGroupMap b t (t ≫ b) rfl ht hs))
    (U : HarrisLevel D) : Function.Surjective (pullClass U) := by
  let := auxiliaryStarRing D C
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  intro xClass
  obtain ⟨x, hx, hnx, rfl⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality (D.harrisTaylorReflexStructure C (b ≫ p)) compatibility h
    t ht htor huT addT L (b ≫ p) xClass
  obtain ⟨Y, hY, hnY, e, he⟩ := hLift x.1 hx hnx
  let W := dualData Y
  have hFrame : Nonempty (Tate.AdelicFrame Y.actionObj.abelianScheme h Y.actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b)) := by
    obtain ⟨eta, _⟩ := Quotient.exists_rep x.2.val
    let isogenyFrames := Tate.adelicFrameIsogeny h
      ((RationalAlgebraAction.pullback b).obj Y.actionObj).action x.1.actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) t
      (RationalAlgebraAction.underlyingIso e) (RationalAlgebraAction.intertwines e.hom)
    exact ⟨Tate.adelicFrameBaseChange b Y.actionObj.abelianScheme h Y.actionObj.action
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) t (isogenyFrames.symm eta.1)⟩
  let Yb := framedPositiveActionBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b Y W.hasDual W.geometry W.inversePoincare W.evaluation
    W.dualEndAdditivity h t hFrame
  have hMultiple : PolarizedWeilLevel.Multiple preservation composition unitCoherence
      associativity comparison symmetry stability square universality addT Yb x.1 1 e :=
    he W
  let levelIso := PolarizedWeilLevel.levelIso preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) t ht htor huT addT Yb x.1
    ((hodgeLevelFunctor D C).obj U) 1 e hMultiple
  obtain ⟨level, hLevel⟩ := framedPositiveActionTowerBaseChange_surjective D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
    Y W hα hFrame U (levelIso.symm x.2)
  let y : DataS U := ⟨Y, level⟩
  refine ⟨mkS y hY hnY, ?_⟩
  rw [classBaseChange_classOf]
  apply (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C (b ≫ p)) compatibility h t ht htor huT addT
    L (b ≫ p) (pullData U y) x _ hx _ hnx).2
  exact ⟨1, e, hMultiple,
    (congrArg levelIso hLevel).trans (levelIso.apply_symm_apply x.2)⟩

end Pointed

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
