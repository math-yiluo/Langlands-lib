import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChangeCoherence
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChangeChoice

/-! # Actual normalized CM pullback along commuting base triangles -/

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

section TransportLaws
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "move" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

@[simp] theorem classTowerPresentationEq_refl (p : S ⟶ Spec (.of F))
    (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y)) :
    move (rfl : p = p) (rfl : s = s) hs hs = 𝟙 _ := rfl

/-- Equality transports compose on the existing normalized tower. -/
@[simp] theorem classTowerPresentationEq_trans
    {p q v : S ⟶ Spec (.of F)} (hpq : p = q) (hqv : q = v)
    {s r u : Spec (.of Ω) ⟶ S} (hsr : s = r) (hru : r = u)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y))
    (hu : ∀ Y : Cover S, Finite (Fiber u Y)) :
    move hpq hsr hs hr ≫ move hqv hru hr hu =
      move (hpq.trans hqv) (hsr.trans hru) hs hu := by
  subst q v r u
  exact Category.id_comp _

end TransportLaws

section Along
variable {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (b : T ⟶ S) (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F))
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω) ⟶ T)
  (hp : b ≫ p = q) (hsquare : t ≫ b = s)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
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

local notation "towerS" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h s hs htor huS addS L p
local notation "towerT" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C q) compatibility h t ht htor huT addT L q
local notation "moveS" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS
local notation "moveT" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huT addT

/-- The existing actual pullback, aligned with both commuting base triangles. -/
def classTowerBaseChangeAlong : towerS ⟶ towerT := by
  subst q s
  exact classTowerBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData p lieS addS addT

/-- Alignment is precisely source and target presentation transport around actual pullback. -/
theorem classTowerBaseChangeAlong_eq
    (hbs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y)) :
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q s t hp hsquare hs ht lieS
      huS huT dualData addS addT =
    moveS rfl hsquare.symm hs hbs ≫
      classTowerBaseChange D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht hbs htor huS huT dualData p lieS addS addT ≫
      moveT hp rfl ht ht := by
  subst q s
  simp only [classTowerBaseChangeAlong, classTowerPresentationEq_refl,
    Category.id_comp, Category.comp_id]

/-- Alignment preserves independence from the constrained dual-evaluation family. -/
theorem classTowerBaseChangeAlong_dualData
    (dualData' : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X) :
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q s t hp hsquare hs ht lieS
      huS huT dualData addS addT =
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q s t hp hsquare hs ht lieS
      huS huT dualData' addS addT := by
  subst q s
  exact classTowerBaseChange_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData dualData'
    p lieS addS addT

end Along

section Identity
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (p : S ⟶ Spec (.of F)) (t : Spec (.of Ω) ⟶ S)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
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

/-- Identity pullback aligned with the two unit triangles is the identity. -/
theorem classTowerBaseChangeAlong_id :
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor (𝟙 S) p p t t
      (Category.id_comp p) (Category.comp_id t) ht ht lieS
      huS huS dualData addS addS = 𝟙 _ := by
  have hs : ∀ Y : Cover S, Finite (Fiber (t ≫ 𝟙 S) Y) := by
    simpa only [Category.comp_id] using ht
  rw [classTowerBaseChangeAlong_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (𝟙 S) p p t t
    (Category.id_comp p) (Category.comp_id t) ht ht lieS
    huS huS dualData addS addS hs]
  rw [classTowerBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor p t ht hs lieS huS dualData addS]
  rw [← Category.assoc, classTowerPresentationEq_trans, classTowerPresentationEq_trans]
  exact classTowerPresentationEq_refl D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor
    huS addS p t ht

end Identity

section Composition
variable {S T R : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  (b : T ⟶ S) (c : R ⟶ T)
  (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F)) (v : R ⟶ Spec (.of F))
  (s : Spec (.of Ω) ⟶ S) (r : Spec (.of Ω) ⟶ T) (t : Spec (.of Ω) ⟶ R)
  (hp : b ≫ p = q) (hq : c ≫ q = v)
  (hr : r ≫ b = s) (ht : t ≫ c = r)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (hrfin : ∀ Y : Cover T, Finite (Fiber r Y))
  (htfin : ∀ Y : Cover R, Finite (Fiber t Y))
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

/-- Successive aligned actual pullbacks equal the pullback along the composite
commuting triangles, for independently supplied constrained dual families. -/
theorem classTowerBaseChangeAlong_comp :
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b p q s r hp hr hs hrfin lieS
      huS huT dualB addS addT ≫
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor c q v r t hq ht hrfin htfin lieT
      huT huR dualC addT addR =
    classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor (c ≫ b) p v s t
      ((Category.assoc c b p).trans ((congrArg (fun k => c ≫ k) hp).trans hq))
      ((Category.assoc t c b).symm.trans ((congrArg (fun k => k ≫ b) ht).trans hr))
      hs htfin lieS huS huR dualD addS addR := by
  subst q v s r
  have hd : ∀ Y : Cover S, Finite (Fiber (t ≫ (c ≫ b)) Y) := by
    simpa only [Category.assoc] using hs
  rw [classTowerBaseChangeAlong_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (c ≫ b) p (c ≫ (b ≫ p))
    ((t ≫ c) ≫ b) t _ _ hs htfin lieS huS huR dualD addS addR hd]
  simpa only [classTowerBaseChangeAlong] using
    (classTowerBaseChange_comp D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor b c p t htfin hrfin hs hd
      lieS lieT huS huT huR dualB dualC dualD addS addT addR)

end Composition

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
