import Langlands.Shimura.PEL.HarrisTaylorCMIntegralExistence
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralUnpointedImage
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedDisconnectedPresheaf

/-! # Full integral-image comparison of the normalized CM presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
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
  (P : Prerequisites.{0})
  (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (htor : TorsionFiniteEtaleStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)

local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "familyTower" => unpointedClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h htor
local notation "familyCondition" => IntegralCMFamilyCondition D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h htor
local notation "imageTower" => integralCMUnpointedClassImageTower D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h htor
local notation "familyPresheaf" => unpointedClassTowerPresheaf D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality P.polarizationBaseChange compatibility h htor
local notation "imagePresheaf" => integralCMUnpointedClassImagePresheaf D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange compatibility h htor

include fibreAmple in
/-- Every point value of each original unpointed CM family has an integral representative. -/
theorem integralCMFamilyCondition_all (X : Bases) {U : HarrisLevel D}
    (x : (familyTower X).obj U) : familyCondition X x := by
  intro a
  exact integralCMClassCondition_all D C P fibreAmple htor X compatibility h
    a.hom a.finiteFibers (x.val a)

include fibreAmple in
/-- The existing integral unpointed image includes bijectively into the full family set. -/
def integralCMUnpointedClassEquiv (X : Bases) (U : HarrisLevel D) :
    (imageTower X).obj U ≃ (familyTower X).obj U where
  toFun := Subtype.val
  invFun x := ⟨x, integralCMFamilyCondition_all D C P fibreAmple htor compatibility h X x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full original Harris level tower is the exact integral-action image. -/
def integralCMUnpointedClassTowerIso (X : Bases) : imageTower X ≅ familyTower X :=
  NatIso.ofComponents
    (fun U => (integralCMUnpointedClassEquiv D C P fibreAmple htor compatibility h X U).toIso)
    (by intros; rfl)

/-- Integral-image comparison is natural on the full connected admissible test category. -/
def integralCMUnpointedClassPresheafIso : imagePresheaf ≅ familyPresheaf :=
  NatIso.ofComponents
    (fun X => integralCMUnpointedClassTowerIso D C P fibreAmple htor compatibility h X.unop)
    (by intros; rfl)

theorem integralCMUnpointedClassPresheafIso_hom :
    (integralCMUnpointedClassPresheafIso D C P fibreAmple htor dualityNaturality
      compatibility h).hom =
    integralCMUnpointedClassImagePresheafInclusion D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality P.polarizationBaseChange compatibility h htor := rfl

open Langlands.AlgebraicGeometry

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality
local notation "component" => componentCMBase D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "componentHom" => componentCMBaseHomTo D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "disTower" => disconnectedClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h htor
local notation "disPull" => disconnectedClassTowerPullback D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  dualityNaturality P.polarizationBaseChange compatibility h htor
local notation "disPresheaf" => disconnectedClassTowerPresheaf D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange compatibility h htor

/-- The original product family has an integral representative at every point
of every actual connected component scheme. -/
def IntegralCMDisconnectedFamilyCondition (X : DisBases) {U : HarrisLevel D}
    (x : (disTower X).obj U) : Prop :=
  ∀ c : _root_.ConnectedComponents X.obj.left, familyCondition (component X c) (x c)

local notation "disCondition" => IntegralCMDisconnectedFamilyCondition D C P htor compatibility h

include fibreAmple in
/-- Every family on a componentwise admissible base lies in the exact integral image. -/
theorem integralCMDisconnectedFamilyCondition_all (X : DisBases) {U : HarrisLevel D}
    (x : (disTower X).obj U) : disCondition X x := by
  intro c
  exact integralCMFamilyCondition_all D C P fibreAmple htor compatibility h (component X c) (x c)

/-- Every original transporter preserves the componentwise integral condition. -/
theorem integralCMDisconnectedFamilyCondition_map (X : DisBases) {U V : HarrisLevel D}
    (f : U ⟶ V) (x : (disTower X).obj U) (hx : disCondition X x) :
    disCondition X ((disTower X).map f x) := by
  intro c
  exact integralCMFamilyCondition_map D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h htor (component X c) f (x c) (hx c)

/-- Actual pullback to each source component preserves the integral condition. -/
theorem integralCMDisconnectedFamilyCondition_pullback {X Y : DisBases} (f : Y ⟶ X)
    {U : HarrisLevel D} (x : (disTower X).obj U) (hx : disCondition X x) :
    disCondition Y ((disPull f).app U x) := by
  intro c
  exact integralCMFamilyCondition_pullback D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    dualityNaturality P.polarizationBaseChange compatibility h htor
    (componentHom f c (componentMap f.hom.left c) rfl)
    (x (componentMap f.hom.left c)) (hx (componentMap f.hom.left c))

/-- The exact integral subimage of the existing disconnected class tower. -/
def IntegralCMDisconnectedClassImageTower (X : DisBases) : HarrisLevel D ⥤ Type 1 where
  obj U := {x : (disTower X).obj U // disCondition X x}
  map f := ↾(fun x => ⟨(disTower X).map f x.val,
    integralCMDisconnectedFamilyCondition_map D C P htor compatibility h X f x.val x.property⟩)
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom ((disTower X).map_id U) x.val
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom ((disTower X).map_comp f g) x.val

local notation "disImageTower" => IntegralCMDisconnectedClassImageTower D C P htor compatibility h

/-- Restrict the original disconnected pullback to its exact integral image. -/
def integralCMDisconnectedClassImagePullback {X Y : DisBases} (f : Y ⟶ X) :
    disImageTower X ⟶ disImageTower Y where
  app U := ↾(fun x => ⟨(disPull f).app U x.val,
    integralCMDisconnectedFamilyCondition_pullback D C P htor dualityNaturality compatibility h
      f x.val x.property⟩)
  naturality {U V} g := by
    ext x
    apply Subtype.ext
    exact (disPull f).naturality_apply g x.val

local notation "disImagePull" => integralCMDisconnectedClassImagePullback D C P htor
  dualityNaturality compatibility h

/-- The componentwise integral image is a presheaf on the full original test category. -/
def integralCMDisconnectedClassImagePresheaf : DisBasesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj X := disImageTower X.unop
  map f := disImagePull f.unop
  map_id X := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((disPresheaf).map_id X)
  map_comp f g := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((disPresheaf).map_comp f g)

local notation "disImagePresheaf" => integralCMDisconnectedClassImagePresheaf D C P htor
  dualityNaturality compatibility h

include fibreAmple in
/-- Forgetting the componentwise integral condition is a bijection at every level. -/
def integralCMDisconnectedClassEquiv (X : DisBases) (U : HarrisLevel D) :
    (disImageTower X).obj U ≃ (disTower X).obj U where
  toFun := Subtype.val
  invFun x := ⟨x,
    integralCMDisconnectedFamilyCondition_all D C P fibreAmple htor compatibility h X x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The integral-image comparison retains all original disconnected level maps. -/
def integralCMDisconnectedClassTowerIso (X : DisBases) : disImageTower X ≅ disTower X :=
  NatIso.ofComponents
    (fun U => (integralCMDisconnectedClassEquiv D C P fibreAmple htor compatibility h X U).toIso)
    (by intros; rfl)

/-- The full normalized disconnected CM presheaf equals its exact integral image,
naturally for every original base morphism and level transporter. -/
def integralCMDisconnectedClassPresheafIso : disImagePresheaf ≅ disPresheaf :=
  NatIso.ofComponents
    (fun X => integralCMDisconnectedClassTowerIso D C P fibreAmple htor compatibility h X.unop)
    (by intros; rfl)

@[simp] theorem integralCMDisconnectedClassPresheafIso_apply
    (X : DisBasesᵒᵖ) (U : HarrisLevel D) (x : (disImageTower X.unop).obj U) :
    ((integralCMDisconnectedClassPresheafIso D C P fibreAmple htor dualityNaturality
      compatibility h).hom.app X).app U x = x.val := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
