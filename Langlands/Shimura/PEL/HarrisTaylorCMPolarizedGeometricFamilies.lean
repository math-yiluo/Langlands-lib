import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointTransport
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Unpointed values from compatible actual geometric-point families -/

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
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

/-- An actual geometric point, with its own algebraically closed field. -/
structure HarrisGeometricPoint (S : Scheme.{0}) where
  (Ω : Type)
  [field : Field Ω]
  [closed : IsAlgClosed Ω]
  hom : Spec (.of Ω) ⟶ S

attribute [instance] HarrisGeometricPoint.field HarrisGeometricPoint.closed

/-- Algebraic closure of the actual residue field supplies a geometric point. -/
def HarrisGeometricPoint.ofResidue (S : Scheme.{0}) (x : S) : HarrisGeometricPoint S where
  Ω := AlgebraicClosure (S.residueField x)
  hom := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField x) (AlgebraicClosure (S.residueField x)))) ≫
      S.fromSpecResidueField x

instance harrisGeometricPointNonempty (S : Scheme.{0}) [Nonempty S] :
    Nonempty (HarrisGeometricPoint S) :=
  ⟨HarrisGeometricPoint.ofResidue S (Classical.arbitrary S)⟩

/-- Push an actual geometric point along a scheme morphism without changing its field. -/
def HarrisGeometricPoint.comp {S T : Scheme.{0}} (a : HarrisGeometricPoint T)
    (b : T ⟶ S) : HarrisGeometricPoint S where
  Ω := a.Ω
  hom := a.hom ≫ b

@[simp] theorem HarrisGeometricPoint.comp_id {S : Scheme.{0}} (a : HarrisGeometricPoint S) :
    a.comp (𝟙 S) = a := by
  change { a with hom := a.hom ≫ 𝟙 S } = a
  simp only [Category.comp_id]

@[simp] theorem HarrisGeometricPoint.comp_comp {S T R : Scheme.{0}}
    (a : HarrisGeometricPoint R) (c : R ⟶ T) (b : T ⟶ S) :
    (a.comp c).comp b = a.comp (c ≫ b) := by
  change { a with hom := (a.hom ≫ c) ≫ b } = { a with hom := a.hom ≫ (c ≫ b) }
  rw [Category.assoc]

/-- Finite fibres are proved for each actual point rather than supplied as extra data. -/
theorem HarrisGeometricPoint.finiteFibers {S : Scheme.{0}} (a : HarrisGeometricPoint S) :
    ∀ Y : Cover S, Finite (Fiber a.hom Y) := geometricFiberFinite a.hom

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
  {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

variable [ConnectedSpace S] [IsLocallyNoetherian S]

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Level" => HarrisLevel D

/-- The existing normalized CM class tower at an actual geometric point. -/
def geometricClassTower (a : HarrisGeometricPoint S) : Level ⥤ Type 1 :=
  HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C p) compatibility h a.hom a.finiteFibers htor
    hu additivity L p

local notation "tower" => geometricClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor hu additivity

/-- Canonical comparison retains each point's actual algebraically closed field. -/
def geometricClassComparison (a b : HarrisGeometricPoint S) : tower a ≅ tower b :=
  classGeometricPointTowerIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity a.hom b.hom a.finiteFibers b.finiteFibers

local notation "move" => geometricClassComparison D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor hu additivity

@[simp] theorem geometricClassComparison_refl (a : HarrisGeometricPoint S) :
    move a a = Iso.refl (tower a) :=
  classGeometricPointTowerIso_refl D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity

theorem geometricClassComparison_trans (a b c : HarrisGeometricPoint S) :
    move a c = move a b ≪≫ move b c :=
  classGeometricPointTowerIso_trans D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p
    compatibility h htor hu additivity

/-- An unpointed class is a family compatible at every pair of actual geometric points. -/
def CompatibleGeometricFamily (U : Level) : Type 1 :=
  { x : (a : HarrisGeometricPoint S) → (tower a).obj U //
    ∀ a b, (move a b).hom.app U (x a) = x b }

local notation "Family" => CompatibleGeometricFamily D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor hu additivity

/-- All original Harris level and Hecke transporters act componentwise on families. -/
def compatibleGeometricFamilyTower : Level ⥤ Type 1 where
  obj := Family
  map f := ↾(fun x => ⟨fun a => (tower a).map f (x.val a), by
    intro a b
    rw [(move a b).hom.naturality_apply f (x.val a), x.property a b]⟩)
  map_id U := by
    ext x
    apply Subtype.ext
    funext a
    exact ConcreteCategory.congr_hom ((tower a).map_id U) (x.val a)
  map_comp f g := by
    ext x
    apply Subtype.ext
    funext a
    exact ConcreteCategory.congr_hom ((tower a).map_comp f g) (x.val a)

local notation "familyTower" => compatibleGeometricFamilyTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

/-- A class at any one point extends by the already constructed canonical comparisons. -/
def geometricFamilyExtension (a : HarrisGeometricPoint S) (U : Level)
    (x : (tower a).obj U) : Family U :=
  ⟨fun b => (move a b).hom.app U x, by
    intro b c
    exact (congrArg (fun k : tower a ≅ tower c => k.hom.app U x)
      (geometricClassComparison_trans D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality p
        compatibility h htor hu additivity a b c)).symm⟩

local notation "extend" => geometricFamilyExtension D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

/-- Evaluation at every geometric point is an actual equivalence, with no chosen point. -/
def geometricFamilyEvaluationEquiv (a : HarrisGeometricPoint S) (U : Level) :
    Family U ≃ (tower a).obj U where
  toFun x := x.val a
  invFun := extend a U
  left_inv x := by
    apply Subtype.ext
    funext b
    exact x.property a b
  right_inv x := by
    change (move a a).hom.app U x = x
    rw [geometricClassComparison_refl]
    rfl

/-- Evaluation recovers the entire original Harris tower, naturally in all its arrows. -/
def geometricFamilyEvaluationIso (a : HarrisGeometricPoint S) : familyTower ≅ tower a :=
  NatIso.ofComponents (fun U => (geometricFamilyEvaluationEquiv D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality p compatibility h htor hu additivity a U).toIso) (by
      intro U V f
      rfl)

local notation "evaluate" => geometricFamilyEvaluationIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor hu additivity

@[simp] theorem geometricFamilyEvaluationIso_hom_app
    (a : HarrisGeometricPoint S) (U : Level) (x : Family U) :
    (evaluate a).hom.app U x = x.val a := rfl

@[simp] theorem geometricFamilyEvaluationIso_inv_app
    (a : HarrisGeometricPoint S) (U : Level) (x : (tower a).obj U) :
    (evaluate a).inv.app U x = extend a U x := rfl

/-- Evaluations at independent point fields agree through canonical point comparison. -/
theorem geometricFamilyEvaluationIso_comparison (a b : HarrisGeometricPoint S) :
    evaluate a ≪≫ move a b = evaluate b := by
  apply Iso.ext
  ext U x
  exact x.property a b

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
