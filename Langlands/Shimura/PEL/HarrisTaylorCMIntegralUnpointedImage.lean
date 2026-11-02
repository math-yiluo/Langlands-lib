import Langlands.Shimura.PEL.HarrisTaylorCMIntegralImageBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralPointComparison
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf

/-! # The exact integral-action image as an unpointed CM subpresheaf -/

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
local notation "familyTower" => unpointedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor
local notation "familyPull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "familyPresheaf" => unpointedClassTowerPresheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "duals" => unpointedPullbackDualData D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

/-- Every point value of the actual compatible family has an integral-action representative. -/
def IntegralCMFamilyCondition (X : Bases) {U : HarrisLevel D}
    (x : (familyTower X).obj U) : Prop :=
  ∀ a : HarrisGeometricPoint X.obj.left,
    IntegralCMClassCondition D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality X.obj.hom compatibility h a.hom
      a.finiteFibers htor X.property.torsionUnits X.property.pairAdditivity (x.val a)

local notation "familyCondition" => IntegralCMFamilyCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor

/-- On an admissible connected base, it suffices to test any one actual geometric point. -/
theorem integralCMFamilyCondition_iff_at (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    {U : HarrisLevel D} (x : (familyTower X).obj U) :
    familyCondition X x ↔
      IntegralCMClassCondition D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality X.obj.hom compatibility h a.hom
        a.finiteFibers htor X.property.torsionUnits X.property.pairAdditivity (x.val a) := by
  constructor
  · exact fun hx => hx a
  · intro hx b
    have hb := integralCMClassCondition_pointMap D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality X.obj.hom compatibility
      h htor X.property.torsionUnits X.property.pairAdditivity
      (Classical.choice (geometricPathExists a.hom b.hom a.finiteFibers b.finiteFibers))
      U (x.val a) hx
    change IntegralCMClassCondition D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality X.obj.hom compatibility h b.hom
      b.finiteFibers htor X.property.torsionUnits X.property.pairAdditivity
      ((geometricClassComparison D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality X.obj.hom compatibility h htor
        X.property.torsionUnits X.property.pairAdditivity a b).hom.app U (x.val a)) at hb
    rw [x.property a b] at hb
    exact hb

/-- The exact integral-action image inside existing actual unpointed CM families. -/
def IntegralCMUnpointedClassImage (X : Bases) (U : HarrisLevel D) :=
  {x : (familyTower X).obj U // familyCondition X x}

local notation "Image" => IntegralCMUnpointedClassImage D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor

/-- The image condition is preserved by every original level transporter. -/
theorem integralCMFamilyCondition_map (X : Bases) {U V : HarrisLevel D} (f : U ⟶ V)
    (x : (familyTower X).obj U) (hx : familyCondition X x) :
    familyCondition X ((familyTower X).map f x) := by
  intro a
  exact integralCMClassCondition_map D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality X.obj.hom compatibility h a.hom
    a.finiteFibers htor X.property.torsionUnits X.property.pairAdditivity f (x.val a) (hx a)

/-- The unpointed integral image retains the full original Harris level tower. -/
def integralCMUnpointedClassImageTower (X : Bases) : HarrisLevel D ⥤ Type 1 where
  obj := Image X
  map f := ↾(fun x => ⟨(familyTower X).map f x.val,
    integralCMFamilyCondition_map D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h htor X f x.val
      x.property⟩)
  map_id U := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((familyTower X).map_id U) x.val
  map_comp f g := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((familyTower X).map_comp f g) x.val

local notation "imageTower" => integralCMUnpointedClassImageTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality compatibility h htor

/-- The unpointed image includes naturally into the original class tower. -/
def integralCMUnpointedClassImageInclusion (X : Bases) : imageTower X ⟶ familyTower X where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

/-- Actual unpointed pullback preserves the exact integral-action image. -/
theorem integralCMFamilyCondition_pullback {X Y : Bases} (f : Y ⟶ X)
    {U : HarrisLevel D} (x : (familyTower X).obj U) (hx : familyCondition X x) :
    familyCondition Y ((familyPull f).app U x) := by
  intro a
  exact integralCMClassCondition_baseChangeAlong D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability f.hom.left compatibility h a.hom a.finiteFibers htor
    X.property.torsionUnits Y.property.torsionUnits (duals f) X.obj.hom
    X.property.lieNaturality X.property.pairAdditivity Y.property.pairAdditivity
    Y.obj.hom (a.comp f.hom.left).hom (Over.w f.hom) rfl
    (a.comp f.hom.left).finiteFibers U (x.val (a.comp f.hom.left)) (hx (a.comp f.hom.left))

/-- Restrict the existing actual unpointed pullback to its integral image tower. -/
def integralCMUnpointedClassImagePullback {X Y : Bases} (f : Y ⟶ X) :
    imageTower X ⟶ imageTower Y where
  app U := ↾(fun x => ⟨(familyPull f).app U x.val,
    integralCMFamilyCondition_pullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor f x.val x.property⟩)
  naturality {U V} g := by
    ext x
    apply Subtype.ext
    exact (familyPull f).naturality_apply g x.val

local notation "imagePull" => integralCMUnpointedClassImagePullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor

/-- The exact integral image is a subpresheaf on the full admissible test category. -/
def integralCMUnpointedClassImagePresheaf : Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj X := imageTower X.unop
  map f := imagePull f.unop
  map_id X := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((familyPresheaf).map_id X)
  map_comp f g := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((familyPresheaf).map_comp f g)

local notation "imagePresheaf" => integralCMUnpointedClassImagePresheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Inclusion is natural both in base morphisms and in every original level arrow. -/
def integralCMUnpointedClassImagePresheafInclusion : imagePresheaf ⟶ familyPresheaf where
  app X := integralCMUnpointedClassImageInclusion D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor X.unop
  naturality _ _ _ := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
