import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeComposition
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange

/-! # Coherence of normalized CM polarized Harris pullback -/

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

section Presentation
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  {p q : S ⟶ Spec (.of F)} (hpq : p = q)
  {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (hr : ∀ Y : Cover S, Finite (Fiber r Y))

local notation "classesP" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h s hs htor huS addS L p
local notation "classesQ" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C q) compatibility h r hr htor huS addS L q
local notation "towerP" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h s hs htor huS addS L p
local notation "towerQ" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C q) compatibility h r hr htor huS addS L q
local notation "moveAmbient" => ambientClassPointEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- Transport equal CM-field structural maps and equal points in the actual
normalized determinant-and-dimension class image. -/
def classPresentationEq (U : HarrisLevel D) : classesP U → classesQ U := by
  subst q r
  exact id

local notation "moveClass" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- The actual ambient polarized quotient changes only by point-equality transport. -/
@[simp] theorem classPresentationEq_val_val (U : HarrisLevel D) (x : classesP U) :
    letI := auxiliaryStarRing D C
    (moveClass hpq hsr hs hr U x).val.val = moveAmbient hsr hs hr U x.val.val := by
  subst q r
  rfl

/-- Equality transport on the existing normalized CM polarized tower. -/
def classTowerPresentationEq : towerP ⟶ towerQ := by
  subst q r
  exact 𝟙 _

local notation "moveTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

@[simp] theorem classTowerPresentationEq_app (U : HarrisLevel D) :
    (moveTower hpq hsr hs hr).app U = ↾(moveClass hpq hsr hs hr U) := by
  subst q r
  rfl

end Presentation

section Identity
variable {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (p : S ⟶ Spec (.of F)) (t : Spec (.of Ω) ⟶ S)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ 𝟙 S) Y))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
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
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (𝟙 S) compatibility h
  t ht hs htor huS huS dualData p lieNaturality addS addS
local notation "pullTower" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (𝟙 S) compatibility h
  t ht hs htor huS huS dualData p lieNaturality addS addS
local notation "moveClass" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS
local notation "moveTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

/-- Actual identity pullback on the existing normalized CM class image is the
canonical transport of its equal structural-map and point presentations. -/
theorem classBaseChange_id (U : HarrisLevel D) :
    pullClass U =
      moveClass (Category.id_comp p).symm (Category.comp_id t) hs ht U := by
  let := auxiliaryStarRing D C
  funext q
  apply Subtype.ext
  apply Subtype.ext
  simp only [classPresentationEq_val_val, classBaseChange_val_val,
    HarrisNumericalWeilLevel.classBaseChange_val,
    HarrisPolarizedWeilLevel.harrisClassBaseChange_val]
  exact congrFun (ambientClassBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h
    t ht hs htor huS dualData addS U) q.val.val

/-- Identity holds on the actual normalized CM tower, with every
original level and Hecke transporter arrow. -/
theorem classTowerBaseChange_id :
    pullTower = moveTower (Category.id_comp p).symm (Category.comp_id t) hs ht := by
  ext U q
  rw [classTowerPresentationEq_app]
  exact congrFun (classBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    p t ht hs lieNaturality huS dualData addS U) q

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
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
  (t ≫ c) htc hs htor huS huT dualB p lieS addS addT
local notation "pullClassC" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h
  t ht htc htor huT huR dualC (b ≫ p) lieT addT addR
local notation "pullClassD" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h
  t ht hd htor huS huR dualD p lieS addS addR
local notation "moveSource" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS
local notation "moveTarget" => classPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huR addR

/-- Successive actual normalized CM pullback equals direct pullback, with
associativity transport of both the source point and target structural map. -/
theorem classBaseChange_comp (U : HarrisLevel D) :
    pullClassC U ∘ pullClassB U =
      moveTarget (Category.assoc c b p) rfl ht ht U ∘ pullClassD U ∘
        moveSource rfl (Category.assoc t c b) hs hd U := by
  let := auxiliaryStarRing D C
  funext q
  apply Subtype.ext
  apply Subtype.ext
  simp only [Function.comp_apply, classPresentationEq_val_val, classBaseChange_val_val,
    HarrisNumericalWeilLevel.classBaseChange_val,
    HarrisPolarizedWeilLevel.harrisClassBaseChange_val]
  exact congrFun (ambientClassBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b c compatibility h
    t ht htc hs hd htor huS huT huR dualB dualC dualD addS addT addR U) q.val.val

local notation "pullTowerB" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
  (t ≫ c) htc hs htor huS huT dualB p lieS addS addT
local notation "pullTowerC" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h
  t ht htc htor huT huR dualC (b ≫ p) lieT addT addR
local notation "pullTowerD" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h
  t ht hd htor huS huR dualD p lieS addS addR
local notation "moveSourceTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS
local notation "moveTargetTower" => classTowerPresentationEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huR addR

/-- Composition on the full existing normalized CM tower retains all original
Harris levels and Hecke transporter arrows. -/
theorem classTowerBaseChange_comp :
    pullTowerB ≫ pullTowerC =
      moveSourceTower rfl (Category.assoc t c b) hs hd ≫ pullTowerD ≫
        moveTargetTower (Category.assoc c b p) rfl ht ht := by
  ext U q
  simp only [NatTrans.comp_app, classTowerPresentationEq_app]
  exact congrFun (classBaseChange_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    b c p t ht htc hs hd lieS lieT huS huT huR dualB dualC dualD addS addT addR U) q

end Composition
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
