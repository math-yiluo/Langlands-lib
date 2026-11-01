import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange
import Langlands.Shimura.PEL.HarrisTaylorLieWeilTower
import Langlands.Shimura.PEL.HarrisTaylorLiePresheaf
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof

/-! # Pointed pullback of actual Harris positive Lie and dimension classes -/

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
  {S T : Scheme.{0}} (b : T ⟶ S)

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

/-- The dual inputs are indexed by the actual pullback of the same source
abelian scheme; no independent changed abelian scheme can be supplied. -/
def PositivePullbackDualData (X : PObjS) : Type 1 :=
  HarrisPolarizedWeilLevel.PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "DataT" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT
local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualAbelianBaseChangeNaturality
  polarizationBaseChange b compatibility h t ht hs htor huS huT dualData

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F] (p : S ⟶ Spec (.of F))

local notation "GoodS" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "GoodT" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)

/-- Pull back one actual polarized level representative with its dimension and positive Lie test. -/
theorem levelDataBaseChange_objectCondition {U : HarrisLevel D} (x : DataS U)
    (hx : GoodS x.1) : GoodT (pullData U x).1 := by
  let := auxiliaryStarRing D C
  exact HarrisTaylor.dimensionLieCondition_pullback L E p b n
    x.1.actionObj.abelianScheme x.1.actionObj.action hx

local notation "pullGood" => levelDataBaseChange_objectCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h t ht hs htor huS huT dualData L p

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "AmbientS" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS addS
local notation "AmbientT" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT addT
local notation "CondS" => ClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "CondT" => ClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT
local notation "pullAmbient" => ambientClassBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h
  t ht hs htor huS huT dualData addS addT

/-- The pulled-back class has the very same satisfying representative, actually base changed. -/
theorem ambientClassBaseChange_condition (U : HarrisLevel D) (q : AmbientS U)
    (hq : CondS q) : CondT (pullAmbient U q) := by
  obtain ⟨x, hx, hgood⟩ := hq
  refine ⟨pullData U x, ?_, pullGood x hgood⟩
  rw [← hx]
  rfl

local notation "ClassesS" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "ClassesT" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT
local notation "mkS" => classOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "mkT" => classOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT

/-- Pointed pullback on the actual polarized dimension-and-positive-Lie class image. -/
def classBaseChange (U : HarrisLevel D) (q : ClassesS U) : ClassesT U :=
  ⟨pullAmbient U q.val, ambientClassBaseChange_condition D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h t ht hs htor huS huT dualData L p addS addT U q.val q.property⟩

local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  t ht hs htor huS huT dualData L p addS addT

@[simp] theorem classBaseChange_val (U : HarrisLevel D) (q : ClassesS U) :
    (pullClass U q).val = pullAmbient U q.val := rfl

/-- The constructor formula retains the source's own actual polarized level representative. -/
@[simp] theorem classBaseChange_classOf (U : HarrisLevel D) (x : DataS U)
    (hx : GoodS x.1) :
    pullClass U (mkS x hx) = mkT (pullData U x) (pullGood x hx) := rfl

local notation "towerS" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "towerT" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT
local notation "pullRawTower" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h
  t ht hs htor huS huT dualData addS addT

/-- Positive Lie and dimension pullback commutes with every original Harris transporter. -/
def classTowerBaseChange : towerS ⟶ towerT where
  app U := ↾(pullClass U)
  naturality {U V} f := by
    ext q
    apply Subtype.ext
    exact NatTrans.naturality_apply pullRawTower f q.val

local notation "pullTower" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  t ht hs htor huS huT dualData L p addS addT
local notation "inclusionS" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "inclusionT" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT

/-- The restricted polarized pullback agrees with the constructed ambient quotient pullback. -/
theorem classTowerBaseChange_inclusion :
    pullTower ≫ inclusionT = inclusionS ≫ pullRawTower := by
  ext U q
  rfl

local notation "forgetS" => forgetDimensionLieAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "forgetT" => forgetDimensionLieAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT

/-- Forgetting the actual polarization and level commutes with the actual action-class pullback. -/
theorem forgetDimensionLieAction_baseChange_val (U : HarrisLevel D) (q : ClassesS U) :
    (forgetT (pullClass U q)).val = RationalAlgebraAction.pullbackClass b (forgetS q).val := by
  obtain ⟨x, hx, hq⟩ := classOf_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p compatibility h
    (t ≫ b) hs htor huS addS q
  rw [← hq]
  rfl

local notation "pullAction" => CategoryTheory.Functor.map
  (HarrisTaylor.dimensionLieActionPresheaf L E n (A := A))
  (Quiver.Hom.op (Over.homMk b rfl : Over.mk (b ≫ p) ⟶ Over.mk p))

/-- The forgetful square uses exactly the existing joint action presheaf's map. -/
theorem forgetDimensionLieAction_baseChange (U : HarrisLevel D) (q : ClassesS U) :
    forgetT (pullClass U q) = pullAction (forgetS q) := by
  apply Subtype.ext
  exact forgetDimensionLieAction_baseChange_val D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    t ht hs htor huS huT dualData L p addS addT U q

/-- The existing action presheaf's pullback, regarded as a map of constant level towers. -/
def actionClassTowerBaseChange :
    (Functor.const (HarrisLevel D)).obj
      (HarrisTaylor.DimensionLieActionClass L E p n (A := A)) ⟶
    (Functor.const (HarrisLevel D)).obj
      (HarrisTaylor.DimensionLieActionClass L E (b ≫ p) n (A := A)) where
  app _ := pullAction
  naturality {_ _} _ := rfl

local notation "forgetTowerS" => forgetDimensionLieActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "forgetTowerT" => forgetDimensionLieActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT

/-- The actual polarized level tower and actual joint action presheaf form a natural square. -/
theorem classTowerBaseChange_forgetDimensionLieAction :
    pullTower ≫ forgetTowerT =
      forgetTowerS ≫ actionClassTowerBaseChange D b L p := by
  ext U q
  exact forgetDimensionLieAction_baseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    t ht hs htor huS huT dualData L p addS addT U q

end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
