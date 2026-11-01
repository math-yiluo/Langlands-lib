import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedAlignedBaseChange
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The actual pointed normalized CM polarized tower presheaf -/

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

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- Actual schemes over the CM spectrum with a point valued in a fixed field. -/
abbrev PointedBase (F Ω : Type) [Field F] [Field Ω] :=
  StructuredArrow (Spec (.of Ω)) (Over.forget (Spec (.of F)))

/-- Explicit conditions on an actual pointed base used by polarized pullback.
The dual premise supplies constrained inputs for actual abelian schemes only. -/
structure AdmissiblePointedBase (X : PointedBase F Ω) : Prop where
  quasiSeparated : QuasiSeparatedSpace X.right.left
  finiteFibers : ∀ Y : Cover X.right.left, Finite (Fiber X.hom Y)
  torsionUnits : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(X.right.left, ⊤))
  muFinite : ∀ k : Index (fun _ => True), IsFinite (mu X.right.left k.val).X.hom
  muEtale : ∀ k : Index (fun _ => True), Etale (mu X.right.left k.val).X.hom
  lieNaturality : LieBaseChangeNaturalityStatement X.right.left
  pairAdditivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := X.right.left)
  dualExists : ∀ B : AbelianScheme X.right.left,
    Nonempty (DualEvaluationData preservation stability B)

/-- The full category of actual pointed bases satisfying the stated conditions. -/
abbrev AdmissiblePointedBaseCategory :=
  ObjectProperty.FullSubcategory
    (AdmissiblePointedBase D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (Ω := Ω))

local notation "Bases" => AdmissiblePointedBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (Ω := Ω)

instance admissiblePointedBaseQuasiSeparated (X : Bases) :
    QuasiSeparatedSpace X.obj.right.left := X.property.quasiSeparated

instance admissiblePointedBaseMuFinite (X : Bases) (k : Index (fun _ => True)) :
    IsFinite (mu X.obj.right.left k.val).X.hom := X.property.muFinite k

instance admissiblePointedBaseMuEtale (X : Bases) (k : Index (fun _ => True)) :
    Etale (mu X.obj.right.left k.val).X.hom := X.property.muEtale k

/-- The existing full normalized polarized class tower at an admissible pointed base. -/
def pointedClassTower (X : Bases) : HarrisLevel D ⥤ Type 1 :=
  HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C X.obj.right.hom) compatibility h
    X.obj.hom X.property.finiteFibers htor X.property.torsionUnits
    X.property.pairAdditivity L X.obj.right.hom

/-- Choice is confined to dual data on the actual pulled-back abelian scheme. -/
def pointedPullbackDualData {X Y : Bases} (f : Y ⟶ X) :
    ∀ Z : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := X.obj.right.left),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality f.hom.right.left Z := by
  letI := auxiliaryStarRing D C
  intro Z
  exact Classical.choice (Y.property.dualExists
    ((Langlands.AbelianScheme.baseChange f.hom.right.left).obj Z.actionObj.abelianScheme))

/-- Actual polarized pullback along a pointed morphism over the CM field. -/
def pointedClassTowerPullback {X Y : Bases} (f : Y ⟶ X) :
    pointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor X ⟶
    pointedClassTower D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor Y :=
  classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor f.hom.right.left
    X.obj.right.hom Y.obj.right.hom X.obj.hom Y.obj.hom
    (Over.w f.hom.right) (StructuredArrow.w f.hom)
    X.property.finiteFibers Y.property.finiteFibers X.property.lieNaturality
    X.property.torsionUnits Y.property.torsionUnits
    (pointedPullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality f)
    X.property.pairAdditivity Y.property.pairAdditivity

local notation "pull" => pointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "duals" => pointedPullbackDualData D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

@[simp] theorem pointedClassTowerPullback_id (X : Bases) : pull (𝟙 X) = 𝟙 _ := by
  exact classTowerBaseChangeAlong_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor X.obj.right.hom X.obj.hom
    X.property.finiteFibers X.property.lieNaturality X.property.torsionUnits
    (duals (𝟙 X)) X.property.pairAdditivity

/-- Functoriality follows for independent choices on each actual pulled scheme. -/
theorem pointedClassTowerPullback_comp {X Y Z : Bases} (f : Y ⟶ X) (g : Z ⟶ Y) :
    pull f ≫ pull g = pull (g ≫ f) := by
  exact classTowerBaseChangeAlong_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor f.hom.right.left g.hom.right.left
    X.obj.right.hom Y.obj.right.hom Z.obj.right.hom X.obj.hom Y.obj.hom Z.obj.hom
    (Over.w f.hom.right) (Over.w g.hom.right)
    (StructuredArrow.w f.hom) (StructuredArrow.w g.hom)
    X.property.finiteFibers Y.property.finiteFibers Z.property.finiteFibers
    X.property.lieNaturality Y.property.lieNaturality
    X.property.torsionUnits Y.property.torsionUnits Z.property.torsionUnits
    (duals f) (duals g) (duals (g ≫ f))
    X.property.pairAdditivity Y.property.pairAdditivity Z.property.pairAdditivity

/-- Contravariant variation in actual admissible pointed CM bases, retaining the
entire original Harris level and Hecke transporter category. -/
def pointedClassTowerPresheaf : Basesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj X := pointedClassTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h htor X.unop
  map f := pull f.unop
  map_id X := pointedClassTowerPullback_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor X.unop
  map_comp f g := (pointedClassTowerPullback_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor f.unop g.unop).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
