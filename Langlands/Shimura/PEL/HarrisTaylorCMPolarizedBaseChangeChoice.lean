import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange
import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeChoice

/-! # Dual-choice independence of actual normalized CM polarized pullback -/

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
  (dualData₁ dualData₂ : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

variable (p : S ⟶ Spec (.of F))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)
local notation "classesS" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "towerS" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "towerT" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C (b ≫ p)) compatibility h t ht htor huT addT L (b ≫ p)
local notation "pullClass₁" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₁ p lieNaturality addS addT
local notation "pullClass₂" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₂ p lieNaturality addS addT

/-- The actual normalized class map is independent of its constrained dual family. -/
theorem classBaseChange_dualData (U : HarrisLevel D) : pullClass₁ U = pullClass₂ U := by
  let := auxiliaryStarRing D C
  funext q
  apply Subtype.ext
  apply Subtype.ext
  simp only [classBaseChange_val_val, HarrisNumericalWeilLevel.classBaseChange_val,
    HarrisPolarizedWeilLevel.harrisClassBaseChange_val]
  exact congrFun (ambientClassBaseChange_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData₁ dualData₂
    addS addT U) q.val.val

local notation "pullTower₁" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₁ p lieNaturality addS addT
local notation "pullTower₂" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₂ p lieNaturality addS addT

/-- Every original Harris transporter component is independent of the dual family. -/
theorem classTowerBaseChange_dualData : pullTower₁ = pullTower₂ := by
  ext U q
  exact congrFun (classBaseChange_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData₁ dualData₂
    p lieNaturality addS addT U) q

/-- Canonical actual normalized pullback from existence of constrained dual inputs. -/
def classTowerBaseChangeOfExists
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X)) :
    towerS ⟶ towerT :=
  classTowerBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) p lieNaturality addS addT

/-- Any actual family computes the canonical existence-based normalized tower map. -/
theorem classTowerBaseChangeOfExists_eq
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT p lieNaturality
      addS addT dualExists = pullTower₁ :=
  classTowerBaseChange_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) dualData₁ p lieNaturality addS addT

/-- The canonical map acts on each class by every supplied actual dual family. -/
@[simp] theorem classTowerBaseChangeOfExists_app
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X))
    (U : HarrisLevel D) (q : classesS U) :
    (classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT p lieNaturality
      addS addT dualExists).app U q = pullClass₁ U q :=
  congrArg (fun (towerMap : towerS ⟶ towerT) => towerMap.app U q)
    (classTowerBaseChangeOfExists_eq D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT dualData₁
      p lieNaturality addS addT dualExists)

local notation "forgetS" => forgetCMActionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p
  compatibility h (t ≫ b) hs htor huS addS
local notation "forgetT" => forgetCMActionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h t ht htor huT addT

/-- Canonical normalized pullback retains the actual joint-action forgetful square. -/
theorem classTowerBaseChangeOfExists_forgetCMAction
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT p lieNaturality
      addS addT dualExists ≫ forgetT =
      forgetS ≫ actionClassTowerBaseChange D C b p lieNaturality :=
  classTowerBaseChange_forgetCMAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) p lieNaturality addS addT

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
