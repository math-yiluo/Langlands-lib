import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedFamilyBaseChange
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The actual unpointed normalized CM polarized tower presheaf -/

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- Explicit geometric prerequisites on an actual unpointed CM base. -/
structure AdmissibleCMBase (X : Over (Spec (.of F))) : Prop where
  connected : ConnectedSpace X.left
  locallyNoetherian : IsLocallyNoetherian X.left
  quasiSeparated : QuasiSeparatedSpace X.left
  torsionUnits : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(X.left, ⊤))
  muFinite : ∀ k : Index (fun _ => True), IsFinite (mu X.left k.val).X.hom
  muEtale : ∀ k : Index (fun _ => True), Etale (mu X.left k.val).X.hom
  lieNaturality : LieBaseChangeNaturalityStatement X.left
  pairAdditivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := X.left)
  dualExists : ∀ B : AbelianScheme X.left,
    Nonempty (DualEvaluationData preservation stability B)

/-- The full category of admissible actual schemes over the CM field. -/
abbrev AdmissibleCMBaseCategory :=
  ObjectProperty.FullSubcategory
    (AdmissibleCMBase D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality)

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

instance admissibleCMBaseConnected (X : Bases) : ConnectedSpace X.obj.left :=
  X.property.connected

instance admissibleCMBaseLocallyNoetherian (X : Bases) : IsLocallyNoetherian X.obj.left :=
  X.property.locallyNoetherian

instance admissibleCMBaseQuasiSeparated (X : Bases) : QuasiSeparatedSpace X.obj.left :=
  X.property.quasiSeparated

instance admissibleCMBaseMuFinite (X : Bases) (k : Index (fun _ => True)) :
    IsFinite (mu X.obj.left k.val).X.hom := X.property.muFinite k

instance admissibleCMBaseMuEtale (X : Bases) (k : Index (fun _ => True)) :
    Etale (mu X.obj.left k.val).X.hom := X.property.muEtale k

/-- Unpointed classes are compatible families at every actual geometric point. -/
def unpointedClassTower (X : Bases) : HarrisLevel D ⥤ Type 1 :=
  compatibleGeometricFamilyTower D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality X.obj.hom
    compatibility h htor X.property.torsionUnits X.property.pairAdditivity

/-- Choose constrained dual data only on the actual pulled-back abelian scheme. -/
def unpointedPullbackDualData {X Y : Bases} (f : Y ⟶ X) :
    ∀ Z : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := X.obj.left),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality f.hom.left Z := by
  letI := auxiliaryStarRing D C
  intro Z
  exact Classical.choice (Y.property.dualExists
    ((Langlands.AbelianScheme.baseChange f.hom.left).obj Z.actionObj.abelianScheme))

/-- Actual contravariant pullback on unpointed CM polarized class towers. -/
def unpointedClassTowerPullback {X Y : Bases} (f : Y ⟶ X) :
    unpointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ⟶
    unpointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor Y :=
  geometricFamilyTowerPullback D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor f.hom.left X.obj.hom Y.obj.hom (Over.w f.hom)
    X.property.lieNaturality X.property.torsionUnits Y.property.torsionUnits
    (unpointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f)
    X.property.pairAdditivity Y.property.pairAdditivity

local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "duals" => unpointedPullbackDualData D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

@[simp] theorem unpointedClassTowerPullback_id (X : Bases) : pull (𝟙 X) = 𝟙 _ :=
  geometricFamilyTowerPullback_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor X.obj.hom X.property.lieNaturality
    X.property.torsionUnits (duals (𝟙 X)) X.property.pairAdditivity

/-- All three arrows may use independently chosen constrained dual data. -/
theorem unpointedClassTowerPullback_comp {X Y Z : Bases} (f : Y ⟶ X) (g : Z ⟶ Y) :
    pull f ≫ pull g = pull (g ≫ f) :=
  geometricFamilyTowerPullback_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor f.hom.left g.hom.left
    X.obj.hom Y.obj.hom Z.obj.hom (Over.w f.hom) (Over.w g.hom)
    X.property.lieNaturality Y.property.lieNaturality
    X.property.torsionUnits Y.property.torsionUnits Z.property.torsionUnits
    (duals f) (duals g) (duals (g ≫ f))
    X.property.pairAdditivity Y.property.pairAdditivity Z.property.pairAdditivity

/-- The actual unpointed tower presheaf on connected locally Noetherian admissible
CM bases, retaining every original Harris level and Hecke transporter arrow. -/
def unpointedClassTowerPresheaf : Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj X := unpointedClassTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h htor X.unop
  map f := pull f.unop
  map_id X := unpointedClassTowerPullback_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor X.unop
  map_comp f g := (unpointedClassTowerPullback_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f.unop g.unop).symm

/-- Evaluation at every actual geometric point recovers the normalized pointed tower. -/
def unpointedClassTowerEvaluationIso (X : Bases) (a : HarrisGeometricPoint X.obj.left) :
    unpointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ≅
    geometricClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality X.obj.hom compatibility h htor
      X.property.torsionUnits X.property.pairAdditivity a :=
  geometricFamilyEvaluationIso D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality X.obj.hom compatibility h htor
    X.property.torsionUnits X.property.pairAdditivity a

/-- Evaluation of actual unpointed pullback is the existing actual pointed pullback. -/
theorem unpointedClassTowerPullback_evaluation {X Y : Bases} (f : Y ⟶ X)
    (a : HarrisGeometricPoint Y.obj.left) :
    pull f ≫ (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      Y a).hom =
    (unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor
      X (a.comp f.hom.left)).hom ≫
    geometricFamilyPointPullback D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor f.hom.left X.obj.hom Y.obj.hom (Over.w f.hom)
      X.property.lieNaturality X.property.torsionUnits Y.property.torsionUnits (duals f)
      X.property.pairAdditivity Y.property.pairAdditivity a := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
