import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointedForgetful

/-! # Natural forgetting from actual unpointed CM polarized towers -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
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

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

/-- Retain the actual CM structure map and every over-category morphism. -/
def unpointedBaseForgetToCM : Bases ⥤ Over (Spec (.of F)) where
  obj X := X.obj
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget the polarization and level at an actual geometric point. -/
def geometricClassTowerForgetCMAction (X : Bases) (a : HarrisGeometricPoint X.obj.left) :
    geometricClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality X.obj.hom compatibility h htor
      X.property.torsionUnits X.property.pairAdditivity a ⟶
    (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C X.obj.hom) :=
  forgetCMActionNatTrans D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality X.obj.hom compatibility h a.hom a.finiteFibers
    htor X.property.torsionUnits X.property.pairAdditivity

local notation "evaluate" => unpointedClassTowerEvaluationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "forgetAt" => geometricClassTowerForgetCMAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- Evaluate a compatible family and forget its polarization and level. -/
def unpointedForgetCMActionAt (X : Bases) (a : HarrisGeometricPoint X.obj.left) :
    unpointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ⟶
    (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C X.obj.hom) :=
  (evaluate X a).hom ≫ forgetAt X a

local notation "forgetFrom" => unpointedForgetCMActionAt D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- Forgetting a compatible family is independent of its actual point and point field. -/
theorem unpointedForgetCMActionAt_independent (X : Bases)
    (a b : HarrisGeometricPoint X.obj.left) : forgetFrom X a = forgetFrom X b := by
  have keep := forgetCMActionNatTrans_classGeometricPointTowerIso D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    X.obj.hom compatibility h htor X.property.torsionUnits X.property.pairAdditivity
    (s := a.hom) (t := b.hom) (hs := a.finiteFibers) (ht := b.finiteFibers)
  have ev := congrArg Iso.hom (geometricFamilyEvaluationIso_comparison D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    X.obj.hom compatibility h htor X.property.torsionUnits X.property.pairAdditivity a b)
  change (evaluate X a).hom ≫ forgetAt X a = (evaluate X b).hom ≫ forgetAt X b
  calc
    (evaluate X a).hom ≫ forgetAt X a =
        (evaluate X a).hom ≫
          ((geometricClassComparison D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality X.obj.hom
            compatibility h htor X.property.torsionUnits X.property.pairAdditivity a b).hom ≫
              forgetAt X b) := congrArg (fun k => (evaluate X a).hom ≫ k) keep.symm
    _ = ((evaluate X a).hom ≫
          (geometricClassComparison D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality X.obj.hom
            compatibility h htor X.property.torsionUnits X.property.pairAdditivity a b).hom) ≫
              forgetAt X b := (Category.assoc _ _ _).symm
    _ = (evaluate X b).hom ≫ forgetAt X b :=
      congrArg (fun k => k ≫ forgetAt X b) ev

variable (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)

/-- Restrict the existing joint CM action presheaf to actual admissible bases. -/
def unpointedActionTowerPresheaf : Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) :=
  (unpointedBaseForgetToCM D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality).op ⋙
      D.harrisTaylorCMActionPresheaf C allNaturality ⋙ Functor.const (HarrisLevel D)

local notation "actionTower" => unpointedActionTowerPresheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality allNaturality

omit [IsCMField F] in
@[simp] theorem unpointedActionTowerPresheaf_obj (X : Bases) :
    (actionTower).obj (Opposite.op X) =
    (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C X.obj.hom) := rfl

omit [IsCMField F] in
@[simp] theorem unpointedActionTowerPresheaf_map_val {X Y : Bases} (f : Y ⟶ X)
    (U : HarrisLevel D) (q : D.HarrisTaylorCMActionClass C X.obj.hom) :
    (((actionTower).map f.op).app U q).val =
      RationalAlgebraAction.pullbackClass f.hom.left q.val := rfl

/-- Use point-independent evaluation; connectedness supplies an actual point. -/
def unpointedForgetCMAction (X : Bases) :
    unpointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ⟶
    (actionTower).obj (Opposite.op X) :=
  forgetFrom X (Classical.arbitrary (HarrisGeometricPoint X.obj.left))

local notation "forget" => unpointedForgetCMAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor allNaturality

/-- The chosen implementation agrees exactly with evaluation at every actual point. -/
theorem unpointedForgetCMAction_eq_evaluation (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) :
    forget X = (evaluate X a).hom ≫ forgetAt X a :=
  unpointedForgetCMActionAt_independent D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor
    X (Classical.arbitrary (HarrisGeometricPoint X.obj.left)) a

/-- Every point computes the same actual joint normalized action class. -/
theorem unpointedForgetCMAction_app (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    (U : HarrisLevel D)
    (x : (unpointedClassTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h htor X).obj U) :
    (forget X).app U x = (forgetAt X a).app U (x.val a) := by
  rw [unpointedForgetCMAction_eq_evaluation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor
    allNaturality X a]
  rfl

local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Actual unpointed pullback commutes with forgetting the polarization and level. -/
theorem unpointedForgetCMAction_naturality {X Y : Bases} (f : Y ⟶ X) :
    pull f ≫ forget Y = forget X ≫ (actionTower).map f.op := by
  let a : HarrisGeometricPoint Y.obj.left := Classical.arbitrary _
  rw [unpointedForgetCMAction_eq_evaluation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      allNaturality Y a,
    unpointedForgetCMAction_eq_evaluation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      allNaturality X (a.comp f.hom.left)]
  have key := classTowerBaseChangeAlong_forgetCMAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f.hom.left
    X.obj.hom Y.obj.hom (Over.w f.hom) X.property.lieNaturality
    (a.comp f.hom.left).hom a.hom rfl
    (a.comp f.hom.left).finiteFibers a.finiteFibers
    X.property.torsionUnits Y.property.torsionUnits
    (unpointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f)
    X.property.pairAdditivity Y.property.pairAdditivity
  ext U x
  apply Subtype.ext
  have kv := congrArg Subtype.val
    (congrFun (congrArg (fun α => α.app U) key) (x.val (a.comp f.hom.left)))
  change _ = (actionClassBaseChangeAlong D C f.hom.left
    X.obj.hom Y.obj.hom (Over.w f.hom) X.property.lieNaturality
    ((forgetAt X (a.comp f.hom.left)).app U (x.val (a.comp f.hom.left)))).val at kv
  rw [actionClassBaseChangeAlong_val] at kv
  exact kv

/-- Natural forgetting in the actual unpointed base and original Harris level variables. -/
def unpointedForgetCMActionNatTrans :
    unpointedClassTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor ⟶ actionTower where
  app X := forget X.unop
  naturality {_ _} f := unpointedForgetCMAction_naturality D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor allNaturality f.unop

@[simp] theorem unpointedForgetCMActionNatTrans_app (X : Bases) :
    (unpointedForgetCMActionNatTrans D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor allNaturality).app (Opposite.op X) =
    forget X := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
