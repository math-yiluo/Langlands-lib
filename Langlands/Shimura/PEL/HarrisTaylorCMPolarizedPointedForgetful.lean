import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointedPresheaf

/-! # Natural forgetting from pointed polarized CM towers -/

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
  {Ω : Type} [Field Ω]
  (htor : TorsionFiniteEtaleStatement.{0})

section Along
variable {S T : Scheme.{0}} (b : T ⟶ S)
  (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F))
  (hp : b ≫ p = q) (lieS : LieBaseChangeNaturalityStatement S)

/-- The existing joint action-class pullback along an actual CM triangle. -/
def actionClassBaseChangeAlong (x : D.HarrisTaylorCMActionClass C p) :
    D.HarrisTaylorCMActionClass C q := by
  subst q
  exact actionClassBaseChange D C b p lieS x

omit [IsCMField F] in
@[simp] theorem actionClassBaseChangeAlong_val (x : D.HarrisTaylorCMActionClass C p) :
    (actionClassBaseChangeAlong D C b p q hp lieS x).val =
      RationalAlgebraAction.pullbackClass b x.val := by
  subst q
  rfl

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω) ⟶ T)
  (hsquare : t ≫ b = s)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ Z : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b Z)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

/-- Alignment by commuting triangles preserves the actual forgetful square. -/
theorem classTowerBaseChangeAlong_forgetCMAction :
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q s t hp hsquare hs ht lieS
      huS huT dualData addS addT ≫
        forgetCMActionNatTrans D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality q compatibility h t ht htor huT addT =
    forgetCMActionNatTrans D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h s hs htor huS addS ≫
        (Functor.const (HarrisLevel D)).map
          (↾(actionClassBaseChangeAlong D C b p q hp lieS)) := by
  subst q s
  exact classTowerBaseChange_forgetCMAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData p lieS addS addT

end Along

local notation "Bases" => AdmissiblePointedBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (Ω := Ω)

/-- Forget the field-valued point and admissibility, retaining the actual CM map. -/
def pointedBaseForgetToCM : Bases ⥤ Over (Spec (.of F)) where
  obj X := X.obj.right
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

variable (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)

/-- Restrict the existing joint CM action presheaf and regard its values as
constant towers on the unchanged Harris level category. -/
def pointedActionTowerPresheaf : Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) :=
  (pointedBaseForgetToCM D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality (Ω := Ω)).op ⋙
      D.harrisTaylorCMActionPresheaf C allNaturality ⋙ Functor.const (HarrisLevel D)

omit [IsCMField F] in
@[simp] theorem pointedActionTowerPresheaf_obj (X : Bases) :
    (pointedActionTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality allNaturality).obj (Opposite.op X) =
    (Functor.const (HarrisLevel D)).obj
      (D.HarrisTaylorCMActionClass C X.obj.right.hom) := rfl

omit [IsCMField F] in
@[simp] theorem pointedActionTowerPresheaf_map_val {X Y : Bases} (f : Y ⟶ X)
    (U : HarrisLevel D) (q : D.HarrisTaylorCMActionClass C X.obj.right.hom) :
    (((pointedActionTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality allNaturality).map f.op).app U q).val =
      RationalAlgebraAction.pullbackClass f.hom.right.left q.val := rfl

/-- At each base, use the existing actual polarization-and-level forgetful map. -/
def pointedForgetCMAction (X : Bases) :
    pointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ⟶
    (pointedActionTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality allNaturality).obj (Opposite.op X) :=
  forgetCMActionNatTrans D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality X.obj.right.hom compatibility h X.obj.hom
    X.property.finiteFibers htor X.property.torsionUnits X.property.pairAdditivity

local notation "pull" => pointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "forget" => pointedForgetCMAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor allNaturality
local notation "actionTower" => pointedActionTowerPresheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  allNaturality (Ω := Ω)

/-- The pointed polarized pullback and existing joint action presheaf commute. -/
theorem pointedForgetCMAction_naturality {X Y : Bases} (f : Y ⟶ X) :
    pull f ≫ forget Y = forget X ≫ (actionTower).map f.op := by
  have key := classTowerBaseChangeAlong_forgetCMAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f.hom.right.left
    X.obj.right.hom Y.obj.right.hom (Over.w f.hom.right) X.property.lieNaturality
    X.obj.hom Y.obj.hom (StructuredArrow.w f.hom)
    X.property.finiteFibers Y.property.finiteFibers
    X.property.torsionUnits Y.property.torsionUnits
    (pointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f)
    X.property.pairAdditivity Y.property.pairAdditivity
  ext U q
  apply Subtype.ext
  have kv := congrArg Subtype.val (congrFun (congrArg (fun α => α.app U) key) q)
  change _ = (actionClassBaseChangeAlong D C f.hom.right.left
    X.obj.right.hom Y.obj.right.hom (Over.w f.hom.right) X.property.lieNaturality
    ((forget X).app U q)).val at kv
  rw [actionClassBaseChangeAlong_val] at kv
  exact kv

/-- Natural forgetting in both the actual base and Harris level variables. -/
def pointedForgetCMActionNatTrans :
    pointedClassTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor ⟶ actionTower where
  app X := forget X.unop
  naturality {_ _} f := pointedForgetCMAction_naturality D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor allNaturality f.unop

@[simp] theorem pointedForgetCMActionNatTrans_app (X : Bases) :
    (pointedForgetCMActionNatTrans D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor allNaturality).app (Opposite.op X) =
    forget X := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
