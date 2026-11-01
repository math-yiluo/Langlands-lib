import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedGeometricFamilies
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedAlignedBaseChange

/-! # Actual base pullback of compatible CM polarized geometric families -/

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
local notation "Level" => HarrisLevel D

section Pullback
variable {S T : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  [ConnectedSpace S] [ConnectedSpace T]
  [IsLocallyNoetherian S] [IsLocallyNoetherian T]
  (b : T ⟶ S) (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F))
  (hp : b ≫ p = q)
  (lieS : LieBaseChangeNaturalityStatement S)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "pointS" => geometricClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor huS addS
local notation "pointT" => geometricClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality q compatibility h htor huT addT
local notation "moveS" => geometricClassComparison D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor huS addS
local notation "moveT" => geometricClassComparison D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality q compatibility h htor huT addT
local notation "familyS" => compatibleGeometricFamilyTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor huS addS
local notation "familyT" => compatibleGeometricFamilyTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  q compatibility h htor huT addT

/-- Pull back a class at the pushed actual point, aligning the structure triangle. -/
def geometricFamilyPointPullback (a : HarrisGeometricPoint T) :
    pointS (a.comp b) ⟶ pointT a :=
  classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor b p q (a.comp b).hom a.hom hp rfl
    (a.comp b).finiteFibers a.finiteFibers lieS huS huT dualData addS addT

local notation "pullAt" => geometricFamilyPointPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor b p q hp lieS
  huS huT dualData addS addT

/-- Canonical point comparison commutes with actual polarized pullback. -/
theorem geometricFamilyPointPullback_comparison (a a' : HarrisGeometricPoint T) :
    (moveS (a.comp b) (a'.comp b)).hom ≫ pullAt a' =
      pullAt a ≫ (moveT a a').hom := by
  subst q
  exact (classTowerGeometricBaseChange_eq_pushed_transport D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h
    (a.comp b).finiteFibers (a'.comp b).finiteFibers htor huS huT dualData p
    lieS addS addT (s := a.hom) (t := a'.hom)
    (hs := a.finiteFibers) (ht := a'.finiteFibers)).symm.trans
      (classTowerGeometricBaseChange_eq_transport D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability b compatibility h
        (a.comp b).finiteFibers htor huS huT dualData p lieS addS addT
        (s := a.hom) (t := a'.hom) (hs := a.finiteFibers) (ht := a'.finiteFibers))

/-- Actual varying-base pullback of all compatible geometric-point families. -/
def geometricFamilyTowerPullback : familyS ⟶ familyT where
  app U := ↾(fun x => ⟨fun a => (pullAt a).app U (x.val (a.comp b)), by
    intro a a'
    have mixed := congrArg
      (fun k : pointS (a.comp b) ⟶ pointT a' => k.app U (x.val (a.comp b)))
      (geometricFamilyPointPullback_comparison D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor b p q hp lieS huS huT dualData
        addS addT a a')
    change (moveT a a').hom.app U ((pullAt a).app U (x.val (a.comp b))) =
      (pullAt a').app U (x.val (a'.comp b))
    rw [← x.property (a.comp b) (a'.comp b)]
    exact mixed.symm⟩)
  naturality U V f := by
    ext x
    apply Subtype.ext
    funext a
    exact (pullAt a).naturality_apply f (x.val (a.comp b))

local notation "pull" => geometricFamilyTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor b p q hp lieS
  huS huT dualData addS addT

@[simp] theorem geometricFamilyTowerPullback_app (U : Level) (x : (familyS).obj U)
    (a : HarrisGeometricPoint T) :
    ((pull).app U x).val a = (pullAt a).app U (x.val (a.comp b)) := rfl

/-- Evaluation computes the existing aligned polarized pullback at every actual point. -/
theorem geometricFamilyTowerPullback_evaluation (a : HarrisGeometricPoint T) :
    pull ≫ (geometricFamilyEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality q compatibility h
      htor huT addT a).hom =
    (geometricFamilyEvaluationIso D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor huS addS
      (a.comp b)).hom ≫ pullAt a := rfl

/-- The unpointed pullback is independent of constrained dual-evaluation choices. -/
theorem geometricFamilyTowerPullback_dualData
    (dualData' : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X) :
    pull = geometricFamilyTowerPullback D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q hp lieS huS huT dualData' addS addT := by
  ext U x
  apply Subtype.ext
  funext a
  exact congrArg (fun k => k.app U (x.val (a.comp b)))
    (classTowerBaseChangeAlong_dualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q (a.comp b).hom a.hom hp rfl
      (a.comp b).finiteFibers a.finiteFibers lieS huS huT dualData addS addT dualData')

end Pullback
section Identity
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  [ConnectedSpace S] [IsLocallyNoetherian S]
  (p : S ⟶ Spec (.of F))
  (lieS : LieBaseChangeNaturalityStatement S)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (𝟙 S) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))


local notation "family" => compatibleGeometricFamilyTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  p compatibility h htor huS addS
local notation "pullId" => geometricFamilyTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor (𝟙 S) p p
  (Category.id_comp p) lieS huS huS dualData addS addS

@[simp] theorem geometricFamilyTowerPullback_id : pullId = 𝟙 (family) := by
  ext U x
  apply Subtype.ext
  funext a
  cases a with
  | mk Ω t =>
    change (classTowerBaseChangeAlong D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor (𝟙 S) p p (t ≫ 𝟙 S) t
      (Category.id_comp p) rfl (HarrisGeometricPoint.finiteFibers ⟨Ω, t ≫ 𝟙 S⟩)
      (HarrisGeometricPoint.finiteFibers ⟨Ω, t⟩) lieS huS huS dualData addS addS).app U
        (x.val ⟨Ω, t ≫ 𝟙 S⟩) = x.val ⟨Ω, t⟩
    exact congrArg (fun k => k.app U (x.val ⟨Ω, t⟩))
      (classTowerBaseChangeAlong_id D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor p t
        (HarrisGeometricPoint.finiteFibers ⟨Ω, t⟩) lieS huS dualData addS)

end Identity
section Composition
variable {S T R : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  [ConnectedSpace S] [ConnectedSpace T] [ConnectedSpace R]
  [IsLocallyNoetherian S] [IsLocallyNoetherian T] [IsLocallyNoetherian R]
  (b : T ⟶ S) (c : R ⟶ T)
  (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F)) (v : R ⟶ Spec (.of F))
  (hp : b ≫ p = q) (hq : c ≫ q = v)
  (lieS : LieBaseChangeNaturalityStatement S)
  (lieT : LieBaseChangeNaturalityStatement T)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  (huR : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(R, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  [hμfinR : ∀ k : Index (fun _ => True), IsFinite (mu R k.val).X.hom]
  [hμetR : ∀ k : Index (fun _ => True), Etale (mu R k.val).X.hom]
  (dualB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b X)
  (dualC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality c X)
  (dualD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (c ≫ b) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))
  (addR : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := R))


local notation "pullB" => geometricFamilyTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor b p q hp lieS
  huS huT dualB addS addT
local notation "pullC" => geometricFamilyTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor c q v hq lieT
  huT huR dualC addT addR
local notation "pullD" => geometricFamilyTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor (c ≫ b) p v
  (Eq.trans (Category.assoc c b p) (Eq.trans (congrArg (fun k => c ≫ k) hp) hq)) lieS
  huS huR dualD addS addR

/-- Unpointed actual pullback composes for independent dual choices on all three arrows. -/
theorem geometricFamilyTowerPullback_comp : pullB ≫ pullC = pullD := by
  ext U x
  apply Subtype.ext
  funext a
  cases a with
  | mk Ω t =>
    exact congrArg (fun k => k.app U (x.val ⟨Ω, (t ≫ c) ≫ b⟩))
      (classTowerBaseChangeAlong_comp D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor b c p q v
        ((t ≫ c) ≫ b) (t ≫ c) t hp hq rfl rfl
        (HarrisGeometricPoint.finiteFibers ⟨Ω, (t ≫ c) ≫ b⟩)
        (HarrisGeometricPoint.finiteFibers ⟨Ω, t ≫ c⟩)
        (HarrisGeometricPoint.finiteFibers ⟨Ω, t⟩)
        lieS lieT huS huT huR dualB dualC dualD addS addT addR)

end Composition
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
