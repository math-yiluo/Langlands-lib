import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeChoice
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeCoherence
import Langlands.AbelianScheme.Tate.WeilLevelBaseChangeCoherence

/-! # Identity of actual Harris polarized level pullback -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open NumberField _root_.Algebra Langlands.AbelianScheme
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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S : Scheme.{0}}

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

variable [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ S)
  (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ 𝟙 S) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (𝟙 S) X)

local notation "DataOld" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ 𝟙 S) hs htor huS
local notation "DataNew" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huS
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (𝟙 S) compatibility h t ht hs htor huS huS dualData

/-- Re-present only the geometric point of an actual Harris level datum along
an equality; the actual polarized object is retained definitionally. -/
def levelDataPointEq {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs' : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y)) (U : HarrisLevel D)
    (x : HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h s hs' htor huS U) :
    HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h r hr htor huS U := by
  let := auxiliaryStarRing D C
  exact ⟨x.1, Tate.weilAdelicLevelPointEq preservation composition unitCoherence associativity
    comparison symmetry stability x.1.hasDual x.1.geometry x.1.inversePoincare
    x.1.evaluation compatibility x.1.polarization h x.1.actionObj.action A
    (D.harrisHodgePELForm C) hsr hs' hr htor huS ((indexFunctor).obj U).toSubgroup x.2⟩

variable (addS : PositivePairAdditivity D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S))

/-- Identity pullback changes the actual positive polarization by the canonical
identity comparison with geometric multiplier one. -/
lemma levelDataBaseChange_id_multiple (U : HarrisLevel D) (x : DataOld U) :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
      comparison symmetry stability square universality addS (pullData U x).1 x.1 1
      (RationalAlgebraAction.pullbackIdIso x.1.actionObj) := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  have hm := rationalDualBaseChangeHom_id_multiple preservation stability composition
    unitCoherence associativity comparison symmetry universality dualAbelianBaseChange
    x.1.actionObj.abelianScheme x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
    W.hasDual W.geometry W.inversePoincare W.evaluation (addS (pullData U x).1 x.1)
    (homToHom0 x.1.polarization)
  rw [rationalDualBaseChangeHom_homToHom0] at hm
  exact hm

/-- On actual fixed level orbits the canonical equivariant identity isogeny
is exactly the existing geometric Tate identity comparison. -/
lemma levelIso_pullbackId (U : HarrisLevel D) (x : DataOld U)
    (z : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) t ht htor huS (pullData U x).1).obj
        ((indexFunctor).obj U)) :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) t ht htor huS addS (pullData U x).1 x.1
      ((indexFunctor).obj U) 1 (RationalAlgebraAction.pullbackIdIso x.1.actionObj)
      (levelDataBaseChange_id_multiple D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h t ht hs htor huS dualData addS U x) z =
    Tate.weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity
      comparison symmetry stability x.1.hasDual x.1.geometry x.1.inversePoincare
      x.1.evaluation compatibility x.1.polarization h x.1.actionObj.action A
      (D.harrisHodgePELForm C) universality (dualData x.1).hasDual
      (dualData x.1).geometry (dualData x.1).inversePoincare (dualData x.1).evaluation
      t ht htor huS ((indexFunctor).obj U).toSubgroup z := by
  let := auxiliaryStarRing D C
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability (pullData U x).1.hasDual (pullData U x).1.geometry
    (pullData U x).1.inversePoincare (pullData U x).1.evaluation
    compatibility (pullData U x).1.polarization h (pullData U x).1.actionObj.action
    A (D.harrisHodgePELForm C) t
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
    compatibility x.1.polarization h x.1.actionObj.action A (D.harrisHodgePELForm C) t
  apply Subtype.ext
  simp only [PolarizedWeilLevel.levelIso, Tate.weilAdelicLevelIsogeny,
    Tate.weilAdelicLevelBaseChangeId, InvariantOrbit.equiv, Equiv.coe_fn_mk,
    InvariantOrbit.map_val]
  apply RightOrbit.map_congr (G := ScalarExtensionSimilitudes A A (Global.FiniteAdeles ℚ)
    (D.harrisHodgePELForm C))
  · apply Tate.weilAdelicFrameIsogeny_right
  · intro eta
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp only [Tate.weilAdelicFrameIsogeny_apply, Tate.weilAdelicFrameBaseChangeId_apply,
      RationalAlgebraAction.underlyingIso_pullbackIdIso]
    exact congrFun (congrArg DFunLike.coe (Tate.rationalHomMap_ofHom
      (Over.mk t) (fun _ => True) (baseChangeIdIso x.1.actionObj.abelianScheme).hom))
      (eta.1 v)

local notation "relAt" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C)
local notation "moveData" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS

/-- The canonical identity comparison relates actual pulled representatives to
the original representatives at the equal geometric point. -/
theorem levelDataBaseChange_id_related (U : HarrisLevel D) (x : DataOld U) :
    letI := auxiliaryStarRing D C
    (relAt t ht htor huS addS ((indexFunctor).obj U)).r (pullData U x)
      (moveData (Category.comp_id t) hs ht U x) := by
  let := auxiliaryStarRing D C
  refine ⟨1, RationalAlgebraAction.pullbackIdIso x.1.actionObj,
    levelDataBaseChange_id_multiple D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h t ht hs htor huS dualData addS U x, ?_⟩
  dsimp only [levelDataPointEq]
  rw [levelIso_pullbackId D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h t ht hs htor huS dualData addS U x]
  exact Tate.weilAdelicLevelBaseChange_id preservation composition unitCoherence
    associativity comparison symmetry stability x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation compatibility x.1.polarization h
    x.1.actionObj.action A (D.harrisHodgePELForm C) universality
    (dualData x.1).hasDual (dualData x.1).geometry (dualData x.1).inversePoincare
    (dualData x.1).evaluation t ht htor huS hs ((indexFunctor).obj U).toSubgroup x.2

/-- Equality transport on ambient Harris polarized classes. -/
def ambientClassPointEq {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs' : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y)) (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    Quotient (relAt s hs' htor huS addS ((indexFunctor).obj U)) →
      Quotient (relAt r hr htor huS addS ((indexFunctor).obj U)) := by
  subst r
  exact id

local notation "moveClass" => ambientClassPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS addS

@[simp] theorem ambientClassPointEq_mk {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs' : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y)) (U : HarrisLevel D)
    (x : HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h s hs' htor huS U) :
    letI := auxiliaryStarRing D C
    moveClass hsr hs' hr U (Quotient.mk _ x) =
      Quotient.mk _ (moveData hsr hs' hr U x) := by
  subst r
  rfl

/-- Actual polarized pullback along the identity is the canonical transport
between the two equal point presentations, for every original Harris level. -/
theorem ambientClassBaseChange_id (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ambientClassBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability (𝟙 S) compatibility h t ht hs htor huS huS dualData addS addS U =
      moveClass (Category.comp_id t) hs ht U := by
  let := auxiliaryStarRing D C
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rw [ambientClassBaseChange_mk, ambientClassPointEq_mk]
  exact Quotient.sound (levelDataBaseChange_id_related D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h t ht hs htor huS dualData addS U x)

/-- The canonical equality transport for the entire original-index class tower. -/
def ambientClassTowerPointEq {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs' : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y)) :
    letI := auxiliaryStarRing D C
    ((hodgeLevelFunctor D C) ⋙ PolarizedWeilLevel.isoClassTower preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h A (D.harrisHodgePELForm C) s hs' htor huS addS) ⟶
    ((hodgeLevelFunctor D C) ⋙ PolarizedWeilLevel.isoClassTower preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h A (D.harrisHodgePELForm C) r hr htor huS addS) := by
  subst r
  exact 𝟙 _

local notation "moveTower" => ambientClassTowerPointEq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor huS addS

@[simp] theorem ambientClassTowerPointEq_app {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs' : ∀ Y : Cover S, Finite (Fiber s Y))
    (hr : ∀ Y : Cover S, Finite (Fiber r Y)) (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    (moveTower hsr hs' hr).app U = ↾(moveClass hsr hs' hr U) := by
  subst r
  rfl

/-- Identity holds as equality of natural transformations, hence also with
all original Harris transition and Hecke arrows. -/
theorem ambientClassTowerBaseChange_id :
    letI := auxiliaryStarRing D C
    ambientClassTowerBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability (𝟙 S) compatibility h t ht hs htor huS huS dualData addS addS =
      moveTower (Category.comp_id t) hs ht := by
  let := auxiliaryStarRing D C
  ext U q
  exact congrFun (ambientClassBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h t ht hs htor huS dualData addS U) q

/-- The identity law also holds for the choice-independent map constructed
from existence of actual dual-evaluation inputs. -/
theorem ambientClassTowerBaseChangeOfExists_id
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality (𝟙 S) X)) :
    letI := auxiliaryStarRing D C
    ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability (𝟙 S) compatibility h t ht hs htor huS huS addS addS dualExists =
      moveTower (Category.comp_id t) hs ht := by
  let := auxiliaryStarRing D C
  exact ambientClassTowerBaseChange_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h t ht hs htor huS
    (fun X => Classical.choice (dualExists X)) addS

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
