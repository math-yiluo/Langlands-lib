import Langlands.Shimura.PEL.HarrisPolarizedNumericalBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedClasses

/-! # Normalized CM pullback of actual polarized Harris towers -/

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

variable (p : S ⟶ Spec (.of F))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexS" => D.harrisTaylorReflexStructure C p
local notation "reflexT" => D.harrisTaylorReflexStructure C (b ≫ p)
local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexS
local notation "GoodT" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexT
local notation "NumS" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
local notation "NumT" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)

include lieNaturality

omit [IsCMField F] in
/-- The determinant of the actual pulled-back representative uses the induced normalized map. -/
theorem levelDataBaseChange_objectCondition {U : HarrisLevel D} (x : DataS U)
    (hx : GoodS x.1) : GoodT (pullData U x).1 := by
  rw [D.harrisTaylorReflexStructure_comp C p b]
  exact HarrisPolarizedWeilLevel.levelDataBaseChange_objectCondition D C hΦ preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
    reflexS lieNaturality x hx

local notation "pullGood" => levelDataBaseChange_objectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData
  p lieNaturality
local notation "pullNum" => HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability b compatibility h t ht hs htor
  huS huT dualData lieNaturality L p
local notation "ClassesS" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexS
  compatibility h (t ≫ b) hs htor huS addS L p
local notation "ClassesT" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexT
  compatibility h t ht htor huT addT L (b ≫ p)
local notation "mkS" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexS
  compatibility h (t ≫ b) hs htor huS addS L p
local notation "mkT" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexT
  compatibility h t ht htor huT addT L (b ≫ p)
local notation "numericalPullClass" => HarrisNumericalWeilLevel.classBaseChange D C hΦ
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
  dualData reflexS lieNaturality L p addS addT

/-- Actual numerical polarized pullback at the single induced normalized CM structure. -/
def classBaseChange (U : HarrisLevel D) (q : ClassesS U) : ClassesT U := by
  let z := numericalPullClass U q
  refine ⟨⟨z.val.val, ?_⟩, ?_⟩
  · simpa only [D.harrisTaylorReflexStructure_comp C p b] using z.val.property
  · obtain ⟨x, hx, hq, hn⟩ := z.property
    refine ⟨x, ?_, ?_, hn⟩
    · simpa only [D.harrisTaylorReflexStructure_comp C p b] using hx
    · apply Subtype.ext
      exact congrArg Subtype.val hq

local notation "pullClass" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieNaturality addS addT

/-- The normalized map retains exactly the ambient constructed polarized quotient value. -/
@[simp] theorem classBaseChange_val_val (U : HarrisLevel D) (q : ClassesS U) :
    (pullClass U q).val.val = (numericalPullClass U q).val.val := rfl

/-- No new representative is selected when passing to the normalized target. -/
@[simp] theorem classBaseChange_classOf (U : HarrisLevel D) (x : DataS U)
    (hx : GoodS x.1) (hn : NumS x.1) :
    pullClass U (mkS x hx hn) =
      mkT (pullData U x) (pullGood x hx) (pullNum x hn) := rfl

local notation "towerS" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexS compatibility h (t ≫ b) hs htor huS addS L p
local notation "towerT" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexT compatibility h t ht htor huT addT L (b ≫ p)
local notation "numericalPullTower" => HarrisNumericalWeilLevel.classTowerBaseChange D C hΦ
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
  dualData reflexS lieNaturality L p addS addT

/-- Pullback between normalized polarized towers is natural for every Harris transporter. -/
def classTowerBaseChange : towerS ⟶ towerT where
  app U := ↾(pullClass U)
  naturality {U V} f := by
    ext q
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val.val) (NatTrans.naturality_apply numericalPullTower f q)

/-- Joint normalized action classes pull back by the actual rational action functor. -/
def actionClassBaseChange (q : D.HarrisTaylorCMActionClass C p) :
    D.HarrisTaylorCMActionClass C (b ≫ p) :=
  ⟨RationalAlgebraAction.pullbackClass b q.val,
    D.harrisTaylorCMActionClassCondition_baseChange_of_naturality C p b
      lieNaturality q.val q.property⟩

local notation "pullAction" => actionClassBaseChange D C b p lieNaturality

omit [IsCMField F] [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  hμfinS hμetS hμfinT hμetT in
@[simp] theorem actionClassBaseChange_val (q : D.HarrisTaylorCMActionClass C p) :
    (pullAction q).val = RationalAlgebraAction.pullbackClass b q.val := rfl

omit [IsCMField F] [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  hμfinS hμetS hμfinT hμetT in
/-- A satisfying action is sent to its own actual base change. -/
@[simp] theorem actionClassBaseChange_classOf (X : RationalAlgebraAction S A)
    (hX : D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action) :
    pullAction (D.harrisTaylorCMActionClassOf C p X hX) =
      D.harrisTaylorCMActionClassOf C (b ≫ p) ((RationalAlgebraAction.pullback b).obj X)
        (D.harrisTaylorCMDeterminantDimensionCondition_baseChange_of_naturality
          C p X.abelianScheme X.action b lieNaturality hX) := rfl

local notation "forgetS" => forgetCMAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  (t ≫ b) hs htor huS addS
local notation "forgetT" => forgetCMAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ p) compatibility h
  t ht htor huT addT

/-- Forgetting the actual polarization and level commutes with normalized action pullback. -/
theorem forgetCMAction_baseChange (U : HarrisLevel D) (q : ClassesS U) :
    forgetT (pullClass U q) = pullAction (forgetS q) := by
  obtain ⟨x, hx, hn, hq⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    reflexS compatibility h (t ≫ b) hs htor huS addS L p q
  rw [← hq]
  apply Subtype.ext
  rfl

/-- The action-class pullback is a map of the constant towers on the same level category. -/
def actionClassTowerBaseChange :
    (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C p) ⟶
      (Functor.const (HarrisLevel D)).obj (D.HarrisTaylorCMActionClass C (b ≫ p)) where
  app _ := ↾pullAction
  naturality {_ _} _ := rfl

local notation "pullTower" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData p lieNaturality addS addT
local notation "forgetTowerS" => forgetCMActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "forgetTowerT" => forgetCMActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT

/-- The constructed normalized polarized and joint action towers form a natural square. -/
theorem classTowerBaseChange_forgetCMAction :
    pullTower ≫ forgetTowerT =
      forgetTowerS ≫ actionClassTowerBaseChange D C b p lieNaturality := by
  ext U q
  exact forgetCMAction_baseChange D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    b compatibility h t ht hs htor huS huT dualData p lieNaturality addS addT U q

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
