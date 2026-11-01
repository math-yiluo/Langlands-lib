import Langlands.Shimura.PEL.HarrisPolarizedDeterminantBaseChangeCoherence
import Langlands.Shimura.PEL.HarrisPolarizedNumericalBaseChange

/-! # Coherence of actual numerical Harris polarized pullback -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisNumericalWeilLevel
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
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (hΦ : IsCMSection E F Φ)
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
  (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L F]

section Presentation
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  {s v : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C))} (hsv : s = v)
  {p q : S ⟶ Spec (.of F)} (hpq : p = q)
  {t r : Spec (.of Ω) ⟶ S} (htr : t = r)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (hr : ∀ Y : Cover S, Finite (Fiber r Y))

local notation "classes" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "tower" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "moveHarris" => harrisClassPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- Transport equal reflex and CM-field structural maps and equal field points
on the existing same-representative numerical subtype. -/
def classPresentationEq (U : HarrisLevel D) :
    classes s compatibility h t ht htor huS addS L p U →
      classes v compatibility h r hr htor huS addS L q U := by
  subst v q r
  exact id

local notation "moveClass" => classPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS

/-- Its determinant-class value is precisely the existing presentation transport. -/
@[simp] theorem classPresentationEq_val (U : HarrisLevel D)
    (x : classes s compatibility h t ht htor huS addS L p U) :
    (moveClass hsv hpq htr ht hr U x).val = moveHarris hsv htr ht hr U x.val := by
  subst v q r
  rfl

/-- Equality transport on the whole existing numerical Harris tower. -/
def classTowerPresentationEq :
    tower s compatibility h t ht htor huS addS L p ⟶
      tower v compatibility h r hr htor huS addS L q := by
  subst v q r
  exact 𝟙 _

local notation "moveTower" => classTowerPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS

@[simp] theorem classTowerPresentationEq_app (U : HarrisLevel D) :
    (moveTower hsv hpq htr ht hr).app U = ↾(moveClass hsv hpq htr ht hr U) := by
  subst v q r
  rfl

end Presentation

section Identity
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (s : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
  (p : S ⟶ Spec (.of F)) (t : Spec (.of Ω) ⟶ S)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ 𝟙 S) Y))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality (𝟙 S) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "pullClass" => classBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (𝟙 S) compatibility h
  t ht hs htor huS huS dualData s lieNaturality L p addS addS
local notation "pullTower" => classTowerBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (𝟙 S) compatibility h
  t ht hs htor huS huS dualData s lieNaturality L p addS addS
local notation "moveClass" => classPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS
local notation "moveTower" => classTowerPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS

/-- Actual numerical identity pullback transports precisely its three equal presentations. -/
theorem classBaseChange_id (U : HarrisLevel D) :
    pullClass U = moveClass (Category.id_comp s).symm
      (Category.id_comp p).symm (Category.comp_id t) hs ht U := by
  funext q
  apply Subtype.ext
  rw [classPresentationEq_val]
  exact congrFun (harrisClassBaseChange_id D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    s t ht hs lieNaturality huS dualData addS U) q.val

/-- Identity on the existing numerical tower, including every original transporter. -/
theorem classTowerBaseChange_id :
    pullTower = moveTower (Category.id_comp s).symm
      (Category.id_comp p).symm (Category.comp_id t) hs ht := by
  ext U q
  rw [classTowerPresentationEq_app]
  exact congrFun (classBaseChange_id D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor L
    s p t ht hs lieNaturality huS dualData addS U) q

end Identity

section Composition
variable {S T R : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  (b : T ⟶ S) (c : R ⟶ T)
  (s : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
  (p : S ⟶ Spec (.of F)) (t : Spec (.of Ω) ⟶ R)
  (ht : ∀ Y : Cover R, Finite (Fiber t Y))
  (htc : ∀ Y : Cover T, Finite (Fiber (t ≫ c) Y))
  (hs : ∀ Y : Cover S, Finite (Fiber ((t ≫ c) ≫ b) Y))
  (hd : ∀ Y : Cover S, Finite (Fiber (t ≫ (c ≫ b)) Y))
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
    PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality b X)
  (dualC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T),
    PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality c X)
  (dualD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality (c ≫ b) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))
  (addR : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := R))

local notation "pullClassB" => classBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
  (t ≫ c) htc hs htor huS huT dualB s lieS L p addS addT
local notation "pullClassC" => classBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h
  t ht htc htor huT huR dualC (b ≫ s) lieT L (b ≫ p) addT addR
local notation "pullClassD" => classBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h
  t ht hd htor huS huR dualD s lieS L p addS addR
local notation "moveSource" => classPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS
local notation "moveTarget" => classPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huR addR

/-- Numerical composition with the source point and both target structure maps transported. -/
theorem classBaseChange_comp (U : HarrisLevel D) :
    pullClassC U ∘ pullClassB U =
      moveTarget (Category.assoc c b s) (Category.assoc c b p) rfl ht ht U ∘
        pullClassD U ∘ moveSource rfl rfl (Category.assoc t c b) hs hd U := by
  funext q
  apply Subtype.ext
  simp only [Function.comp_apply, classPresentationEq_val, classBaseChange_val]
  exact congrFun (harrisClassBaseChange_comp D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    b c s t ht htc hs hd lieS lieT huS huT huR dualB dualC dualD addS addT addR U) q.val

local notation "pullTowerB" => classTowerBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
  (t ≫ c) htc hs htor huS huT dualB s lieS L p addS addT
local notation "pullTowerC" => classTowerBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h
  t ht htc htor huT huR dualC (b ≫ s) lieT L (b ≫ p) addT addR
local notation "pullTowerD" => classTowerBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h
  t ht hd htor huS huR dualD s lieS L p addS addR
local notation "moveSourceTower" => classTowerPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huS addS
local notation "moveTargetTower" => classTowerPresentationEq D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor L huR addR

/-- The numerical composition equation on the full original Harris tower. -/
theorem classTowerBaseChange_comp :
    pullTowerB ≫ pullTowerC =
      moveSourceTower rfl rfl (Category.assoc t c b) hs hd ≫ pullTowerD ≫
        moveTargetTower (Category.assoc c b s) (Category.assoc c b p) rfl ht ht := by
  ext U q
  simp only [NatTrans.comp_app, classTowerPresentationEq_app]
  exact congrFun (classBaseChange_comp D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor L
    b c s p t ht htc hs hd lieS lieT huS huT huR dualB dualC dualD addS addT addR U) q

end Composition
end Langlands.Shimura.PEL.HarrisNumericalWeilLevel
