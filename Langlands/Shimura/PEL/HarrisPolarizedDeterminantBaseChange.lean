import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange
import Langlands.Shimura.PEL.RationalLieDeterminantBaseChange

/-! # Determinant-compatible pointed Harris polarized pullback -/

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
  {S T : Scheme.{0}} (b : T ⟶ S)

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
local notation "indexFunctor" => hodgeLevelFunctor D C

local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

variable (s : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
  (lieNaturality : LieBaseChangeNaturalityStatement S)

include lieNaturality

local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality s
local notation "GoodT" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ s)

/-- The exact constructed representative satisfies the pulled-back Harris determinant
condition; no condition on an independently supplied target object is used. -/
theorem levelDataBaseChange_objectCondition {U : HarrisLevel D} (x : DataS U)
    (hx : GoodS x.1) : GoodT (pullData U x).1 := by
  let := auxiliaryStarRing D C
  exact D.harrisRationalLieDeterminantCondition_baseChange_of_naturality
    C hΦ s x.1.actionObj.abelianScheme x.1.actionObj.action b lieNaturality hx

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "pullClass" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData addS addT
local notation "CondS" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS
local notation "CondT" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT
local notation "AmbientS" => PolarizedWeilLevel.IsoClass preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h A
  (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS

/-- The determinant predicate is preserved by the already constructed ambient quotient map. -/
theorem ambientClassBaseChange_condition (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (q : AmbientS ((indexFunctor).obj U)), CondS q → CondT (pullClass U q) := by
  let := auxiliaryStarRing D C
  change ∀ (q : AmbientS ((indexFunctor).obj U)), CondS q → CondT (pullClass U q)
  intro q
  refine Quotient.inductionOn q ?_
  intro x hx
  exact levelDataBaseChange_objectCondition D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData s lieNaturality x hx

local notation "ClassesS" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS
local notation "ClassesT" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT
local notation "mkS" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS
local notation "mkT" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT
local notation "pullGood" => levelDataBaseChange_objectCondition D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData s
  lieNaturality

/-- Restrict actual pointed class pullback to the existing Harris determinant classes. -/
def harrisClassBaseChange (U : HarrisLevel D) (q : ClassesS U) : ClassesT U := by
  let := auxiliaryStarRing D C
  exact ⟨pullClass U q.val, ambientClassBaseChange_condition D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
    s lieNaturality addS addT U q.val q.property⟩

local notation "pullHarris" => harrisClassBaseChange D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality addS addT

@[simp] theorem harrisClassBaseChange_val (U : HarrisLevel D) (q : ClassesS U) :
    letI := auxiliaryStarRing D C
    (pullHarris U q).val = pullClass U q.val := rfl

/-- On an actual satisfying representative the map uses precisely its constructed pullback. -/
@[simp] theorem harrisClassBaseChange_classOf (U : HarrisLevel D) (x : DataS U)
    (hx : GoodS x.1) :
    pullHarris U (mkS x hx) = mkT (pullData U x) (pullGood x hx) := rfl

local notation "towerS" => harrisIsoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS
local notation "towerT" => harrisIsoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT
local notation "ambientPullback" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData addS addT

/-- Determinant-compatible class pullback is natural for every original Harris transporter. -/
def harrisClassTowerBaseChange : towerS ⟶ towerT where
  app U := ↾(pullHarris U)
  naturality {U V} f := by
    ext q
    apply Subtype.ext
    exact NatTrans.naturality_apply ambientPullback f q.val

local notation "harrisPullback" => harrisClassTowerBaseChange D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality addS addT
local notation "inclusionS" => harrisInclusionNatTrans D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality s
  compatibility h (t ≫ b) hs htor huS addS
local notation "inclusionT" => harrisInclusionNatTrans D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ s)
  compatibility h t ht htor huT addT

/-- The restricted pullback commutes with the natural inclusion into ambient polarized classes. -/
theorem harrisClassTowerBaseChange_inclusion :
    letI := auxiliaryStarRing D C
    harrisPullback ≫ inclusionT = inclusionS ≫ ambientPullback := by
  let := auxiliaryStarRing D C
  ext U q
  rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
