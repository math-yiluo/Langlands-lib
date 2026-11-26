import Langlands.Shimura.PEL.HarrisTaylorCMArtinianClassReduction

/-! # Pointed restriction of normalized Harris classes from lifts up to a rational multiple -/

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
local notation "Pos" base => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := base)

/-- An equivariant rational isomorphism from the restriction of `X` to `Y`
carries the polarization of `Y` to `q` times the actual base change of the
polarization of `X`, for every constrained choice of dual data on the
restricted abelian scheme. -/
def PositivePolarizedActionReductionMultiple
    {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
    (b : T ⟶ S) (X : Pos S) (Y : Pos T) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ((RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj) → Prop :=
  letI := auxiliaryStarRing D C
  fun e => ∀ W : PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality b X,
    let lam := dualAbelianBaseChangeMap preservation stability composition unitCoherence
      associativity comparison symmetry universality dualAbelianBaseChange b
      X.actionObj.abelianScheme X.hasDual X.geometry X.inversePoincare X.evaluation
      W.hasDual W.geometry W.inversePoincare W.evaluation X.polarization
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability W.hasDual Y.hasDual W.geometry Y.geometry
      W.inversePoincare W.evaluation Y.inversePoincare Y.evaluation
      (relativeDualSchemeMapAdditivity preservation stability T _ _ W.hasDual Y.hasDual)
      (q : ℚ) (RationalAlgebraAction.underlyingIso e).hom
      (Rationalization.ofHom lam) (Rationalization.ofHom Y.polarization)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The isometric reduction of the Artinian criterion is the multiplier-one case. -/
theorem positivePolarizedActionReductionMultiple_one_iff
    {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
    (b : T ⟶ S) (X : Pos S) (Y : Pos T)
    (e : letI := auxiliaryStarRing D C
      (RationalAlgebraAction.pullback b).obj X.actionObj ≅ Y.actionObj) :
    PositivePolarizedActionReductionMultiple D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X Y 1 e ↔
      PositivePolarizedActionIsometricReduction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X Y e :=
  Iff.rfl

section Pointed

variable {S T : Scheme.{0}} (b : T ⟶ S) (p : S ⟶ Spec (.of F))
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]

local notation "PObjS" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)
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
local notation "DataT" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT
local notation "mkS" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieS addS addT
local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- At a fixed Harris level, lifts of the representatives of lower classes up to a
rational multiple of the polarization, together with surjectivity on pointed
monodromy, make the pointed normalized class restriction surjective. -/
theorem classBaseChange_surjective_of_levelMultipleLifts (U : HarrisLevel D)
    (hLift : letI := auxiliaryStarRing D C
      ∀ x : DataT U, GoodT x.1 → NumT x.1 →
        ∃ Y : PObjS, GoodS Y ∧ NumS Y ∧ ∃ (q : ℚˣ)
          (e : (RationalAlgebraAction.pullback b).obj Y.actionObj ≅ x.1.actionObj),
          PositivePolarizedActionReductionMultiple D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality b Y x.1 q e)
    (hα : Function.Surjective (fundamentalGroupMap b t (t ≫ b) rfl ht hs)) :
    Function.Surjective (pullClass U) := by
  let := auxiliaryStarRing D C
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  intro xClass
  obtain ⟨x, hx, hnx, rfl⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality (D.harrisTaylorReflexStructure C (b ≫ p)) compatibility h
    t ht htor huT addT L (b ≫ p) xClass
  obtain ⟨Y, hY, hnY, q, e, he⟩ := hLift x hx hnx
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
      associativity comparison symmetry stability square universality addT Yb x.1 q e :=
    he W
  let levelIso := PolarizedWeilLevel.levelIso preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) t ht htor huT addT Yb x.1
    ((hodgeLevelFunctor D C).obj U) q e hMultiple
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
  exact ⟨q, e, hMultiple,
    (congrArg levelIso hLevel).trans (levelIso.apply_symm_apply x.2)⟩

end Pointed

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
