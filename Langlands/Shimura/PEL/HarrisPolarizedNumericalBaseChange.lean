import Langlands.Shimura.PEL.HarrisPolarizedDeterminantBaseChange
import Langlands.Shimura.PEL.HarrisNumericalWeilTower
import Langlands.Shimura.PEL.HarrisTaylorLieBaseChange

/-! # Numerical pointed Harris polarized class pullback -/

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
  (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L F]
  (p : S ⟶ Spec (.of F))

include lieNaturality

local notation "NumS" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "NumT" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)

omit [IsScalarTower ℚ F A] in
/-- The actual pulled-back representative retains its geometric dimension and central trace. -/
theorem levelDataBaseChange_numericalObjectCondition {U : HarrisLevel D} (x : DataS U)
    (hx : NumS x.1) : NumT (pullData U x).1 := by
  let := auxiliaryStarRing D C
  exact HarrisTaylor.numericalCondition_baseChange_of_naturality L F p
    x.1.actionObj.abelianScheme x.1.actionObj.action n b lieNaturality E hx

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality s
local notation "GoodT" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ s)
local notation "pullGood" => HarrisPolarizedWeilLevel.levelDataBaseChange_objectCondition
  D C hΦ preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability b compatibility h
  t ht hs htor huS huT dualData s lieNaturality
local notation "pullNum" => levelDataBaseChange_numericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  lieNaturality L p
local notation "pullHarris" => harrisClassBaseChange D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality addS addT
local notation "HarrisS" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS
local notation "HarrisT" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT
local notation "CondS" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS L p
local notation "CondT" => ClassCondition D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT L (b ≫ p)

/-- The same satisfying representative proves preservation of the numerical image. -/
theorem harrisClassBaseChange_condition (U : HarrisLevel D) (q : HarrisS U)
    (hq : CondS q) : CondT (pullHarris U q) := by
  obtain ⟨x, hx, hq, hn⟩ := hq
  refine ⟨pullData U x, pullGood x hx, ?_, pullNum x hn⟩
  rw [← hq]
  rfl

local notation "ClassesS" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS L p
local notation "ClassesT" => IsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT L (b ≫ p)
local notation "mkS" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS L p
local notation "mkT" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT L (b ≫ p)

/-- Actual pointed base change restricts to numerical Harris polarized classes. -/
def classBaseChange (U : HarrisLevel D) (q : ClassesS U) : ClassesT U :=
  ⟨pullHarris U q.val, harrisClassBaseChange_condition D C hΦ preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
    s lieNaturality L p addS addT U q.val q.property⟩

local notation "pullClass" => classBaseChange D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality L p addS addT

@[simp] theorem classBaseChange_val (U : HarrisLevel D) (q : ClassesS U) :
    (pullClass U q).val = pullHarris U q.val := rfl

/-- The output uses exactly the source representative's constructed pullback. -/
@[simp] theorem classBaseChange_classOf (U : HarrisLevel D) (x : DataS U)
    (hx : GoodS x.1) (hn : NumS x.1) :
    pullClass U (mkS x hx hn) =
      mkT (pullData U x) (pullGood x hx) (pullNum x hn) := rfl

local notation "towerS" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality s compatibility h
  (t ≫ b) hs htor huS addS L p
local notation "towerT" => isoClassTower D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ s) compatibility h
  t ht htor huT addT L (b ≫ p)
local notation "harrisPullback" => harrisClassTowerBaseChange D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality addS addT

/-- Numerical class pullback is natural for every original Harris transporter. -/
def classTowerBaseChange : towerS ⟶ towerT where
  app U := ↾(pullClass U)
  naturality {U V} f := by
    ext q
    apply Subtype.ext
    exact NatTrans.naturality_apply harrisPullback f q.val

local notation "numericalPullback" => classTowerBaseChange D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  s lieNaturality L p addS addT
local notation "inclusionS" => inclusionNatTrans D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality s
  compatibility h (t ≫ b) hs htor huS addS L p
local notation "inclusionT" => inclusionNatTrans D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ s)
  compatibility h t ht htor huT addT L (b ≫ p)

/-- The numerical restriction commutes with inclusion into the determinant tower. -/
theorem classTowerBaseChange_inclusion :
    numericalPullback ≫ inclusionT = inclusionS ≫ harrisPullback := by
  ext U q
  rfl

end Langlands.Shimura.PEL.HarrisNumericalWeilLevel
