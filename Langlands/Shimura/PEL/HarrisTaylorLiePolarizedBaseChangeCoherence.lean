import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeComposition
import Langlands.Shimura.PEL.HarrisTaylorLieBaseChangeChoice

/-! # Coherence of actual Harris positive Lie and dimension pullback -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω]
  (htor : TorsionFiniteEtaleStatement.{0})

section Presentation
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  {p q : S ⟶ Spec (.of F)} (hp : p = q)
  {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (hr : ∀ Y : Cover S, Finite (Fiber r Y))

local notation "classes" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L
local notation "tower" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L
local notation "moveAmbient" => ambientClassPointEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- Re-present equal structural maps and equal field points on the actual
dimension-and-positive-Lie class image. -/
def classPresentationEq (U : HarrisLevel D) :
    classes p compatibility h s hs htor huS addS U →
      classes q compatibility h r hr htor huS addS U := by
  subst q r
  exact id

local notation "moveClass" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS

/-- The underlying polarized class changes only by the actual point-equality transport. -/
@[simp] theorem classPresentationEq_val (U : HarrisLevel D)
    (x : classes p compatibility h s hs htor huS addS U) :
    letI := auxiliaryStarRing D C
    (moveClass hp hsr hs hr U x).val = moveAmbient hsr hs hr U x.val := by
  subst q r
  rfl

/-- Equality transport on the whole existing original-Harris restricted tower. -/
def classTowerPresentationEq :
    tower p compatibility h s hs htor huS addS ⟶
      tower q compatibility h r hr htor huS addS := by
  subst q r
  exact 𝟙 _

local notation "moveTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS

@[simp] theorem classTowerPresentationEq_app (U : HarrisLevel D) :
    (moveTower hp hsr hs hr).app U = ↾(moveClass hp hsr hs hr U) := by
  subst q r
  rfl

end Presentation

section Identity
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (p : S ⟶ Spec (.of F)) (t : Spec (.of Ω) ⟶ S)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ 𝟙 S) Y))
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality (𝟙 S) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (𝟙 S) compatibility h
  t ht hs htor huS huS dualData L p addS addS
local notation "pullTower" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (𝟙 S) compatibility h
  t ht hs htor huS huS dualData L p addS addS
local notation "moveClass" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS
local notation "moveTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS

/-- Actual identity pullback on the existing restricted class image is the
canonical transport of its equal structural-map and point presentations. -/
theorem classBaseChange_id (U : HarrisLevel D) :
    pullClass U =
      moveClass (Category.id_comp p).symm (Category.comp_id t) hs ht U := by
  let := auxiliaryStarRing D C
  funext q
  apply Subtype.ext
  rw [classPresentationEq_val]
  exact congrFun (ambientClassBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    dualAbelianBaseChangeNaturality polarizationBaseChange compatibility h
    t ht hs htor huS dualData addS U) q.val

/-- Identity holds on the actual positive Lie and dimension tower, with every
original level and Hecke transporter arrow. -/
theorem classTowerBaseChange_id :
    pullTower = moveTower (Category.id_comp p).symm (Category.comp_id t) hs ht := by
  ext U q
  rw [classTowerPresentationEq_app]
  exact congrFun (classBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L compatibility h htor
    p t ht hs huS dualData addS U) q

/-- The same identity law holds for the existing choice-independent constructor
from existence of actual dual-evaluation inputs. -/
theorem classTowerBaseChangeOfExists_id
    (dualExists : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      Nonempty (HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality (𝟙 S) X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (𝟙 S) compatibility h
      t ht hs htor huS huS L p addS addS dualExists =
    moveTower (Category.id_comp p).symm (Category.comp_id t) hs ht := by
  exact classTowerBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L compatibility h htor
    p t ht hs huS (fun X => Classical.choice (dualExists X)) addS

end Identity

section Composition
variable {S T R : Scheme.{0}}
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  (b : T ⟶ S) (c : R ⟶ T) (p : S ⟶ Spec (.of F))
  (t : Spec (.of Ω) ⟶ R)
  (ht : ∀ Y : Cover R, Finite (Fiber t Y))
  (htc : ∀ Y : Cover T, Finite (Fiber (t ≫ c) Y))
  (hs : ∀ Y : Cover S, Finite (Fiber ((t ≫ c) ≫ b) Y))
  (hd : ∀ Y : Cover S, Finite (Fiber (t ≫ (c ≫ b)) Y))
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
    HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality b X)
  (dualC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T),
    HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality c X)
  (dualD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality (c ≫ b) X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))
  (addR : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := R))

local notation "pullClassB" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  (t ≫ c) htc hs htor huS huT dualB L p addS addT
local notation "pullClassC" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality c compatibility h
  t ht htc htor huT huR dualC L (b ≫ p) addT addR
local notation "pullClassD" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (c ≫ b) compatibility h
  t ht hd htor huS huR dualD L p addS addR
local notation "moveSource" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS
local notation "moveTarget" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huR addR

/-- Successive actual restricted pullback equals direct pullback, with
associativity transport of both the source point and target structural map. -/
theorem classBaseChange_comp (U : HarrisLevel D) :
    pullClassC U ∘ pullClassB U =
      moveTarget (Category.assoc c b p) rfl ht ht U ∘ pullClassD U ∘
        moveSource rfl (Category.assoc t c b) hs hd U := by
  let := auxiliaryStarRing D C
  funext q
  apply Subtype.ext
  simp only [Function.comp_apply, classPresentationEq_val, classBaseChange_val]
  exact congrFun (ambientClassBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    dualAbelianBaseChangeNaturality polarizationBaseChange b c compatibility h
    t ht htc hs hd htor huS huT huR dualB dualC dualD addS addT addR U) q.val

local notation "pullTowerB" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  (t ≫ c) htc hs htor huS huT dualB L p addS addT
local notation "pullTowerC" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality c compatibility h
  t ht htc htor huT huR dualC L (b ≫ p) addT addR
local notation "pullTowerD" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (c ≫ b) compatibility h
  t ht hd htor huS huR dualD L p addS addR
local notation "moveSourceTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huS addS
local notation "moveTargetTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  L compatibility h htor huR addR

/-- Composition on the full existing restricted tower retains all original
Harris levels and Hecke transporter arrows. -/
theorem classTowerBaseChange_comp :
    pullTowerB ≫ pullTowerC =
      moveSourceTower rfl (Category.assoc t c b) hs hd ≫ pullTowerD ≫
        moveTargetTower (Category.assoc c b p) rfl ht ht := by
  ext U q
  simp only [NatTrans.comp_app, classTowerPresentationEq_app]
  exact congrFun (classBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L compatibility h htor
    b c p t ht htc hs hd huS huT huR dualB dualC dualD addS addT addR U) q

/-- The same composition law holds for the existing constructor from
existence of actual constrained dual-evaluation families. -/
theorem classTowerBaseChangeOfExists_comp
    (existsB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      Nonempty (HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality b X))
    (existsC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := T),
      Nonempty (HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality c X))
    (existsD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := S),
      Nonempty (HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality (c ≫ b) X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      (t ≫ c) htc hs htor huS huT L p addS addT existsB ≫
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality c compatibility h
      t ht htc htor huT huR L (b ≫ p) addT addR existsC =
    moveSourceTower rfl (Category.assoc t c b) hs hd ≫
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (c ≫ b) compatibility h
      t ht hd htor huS huR L p addS addR existsD ≫
    moveTargetTower (Category.assoc c b p) rfl ht ht := by
  exact classTowerBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L compatibility h htor
    b c p t ht htc hs hd huS huT huR
    (fun X => Classical.choice (existsB X))
    (fun X => Classical.choice (existsC X))
    (fun X => Classical.choice (existsD X)) addS addT addR

end Composition
end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
