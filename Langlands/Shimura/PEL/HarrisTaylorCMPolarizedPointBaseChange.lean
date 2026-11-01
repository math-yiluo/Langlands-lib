import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPointTransport
import Langlands.Shimura.PEL.HarrisTaylorLiePointBaseChange

/-! # Mixed point and base pullback of normalized CM polarized Harris classes -/

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
  {Ω Ω' : Type} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ T} {t : Spec (.of Ω') ⟶ T}
  {hs : ∀ Y : Cover T, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover T, Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
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

variable
  (p : S ⟶ Spec (.of F))
  (lieNaturality : LieBaseChangeNaturalityStatement S)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Level" => HarrisLevel D
local notation "reflexS" => D.harrisTaylorReflexStructure C p
local notation "reflexT" => D.harrisTaylorReflexStructure C (b ≫ p)
local notation "classesSAt" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexS compatibility h
local notation "classesTAt" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexT compatibility h
local notation "towerSAt" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexS compatibility h
local notation "towerTAt" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexT compatibility h
local notation "pullClassAt" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
local notation "pullTowerAt" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h
local notation "moveClassS" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor huS addS
local notation "moveClassT" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h htor huT addT
local notation "moveTowerS" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h htor huS addS
local notation "moveTowerT" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h htor huT addT

/-- The normalized double image retains the actual ambient mixed point/base-change square. -/
theorem classBaseChange_pointMap
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesSAt (s ≫ b) hsb htor huS addS L p U) :
    pullClassAt t ht htb htor huS huT dualData p lieNaturality addS addT U
        (moveClassS (pathPushforward b hsb htb epath) U q) =
      moveClassT epath U
        (pullClassAt s hs hsb htor huS huT dualData p lieNaturality addS addT U q) := by
  apply Subtype.ext
  apply Subtype.ext
  exact HarrisTaylorLieWeilLevel.ambientClassBaseChange_pointMap D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b
    compatibility h hsb htb htor huS huT dualData addS addT epath U q.val.val

/-- Normalized polarized pullback and point comparison commute on every original Harris level. -/
theorem classTowerBaseChange_pointTransport
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTowerS (pathPushforward b hsb htb epath)).hom ≫
        pullTowerAt t ht htb htor huS huT dualData p lieNaturality addS addT =
      pullTowerAt s hs hsb htor huS huT dualData p lieNaturality addS addT ≫
        (moveTowerT epath).hom := by
  ext U q
  exact classBaseChange_pointMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    b compatibility h hsb htb htor huS huT dualData p lieNaturality addS addT epath U q

/-- Actual normalized CM pullback followed by comparison with a second point presentation. -/
def classTowerBaseChangeAlongPath (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerSAt (s ≫ b) hsb htor huS addS L p ⟶
      towerTAt t ht htor huT addT L (b ≫ p) :=
  pullTowerAt s hs hsb htor huS huT dualData p lieNaturality addS addT ≫ (moveTowerT epath).hom

local notation "diagonal" => classTowerBaseChangeAlongPath D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h hsb htor huS huT dualData p
  lieNaturality addS addT

@[simp] theorem classTowerBaseChangeAlongPath_app
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesSAt (s ≫ b) hsb htor huS addS L p U) :
    (diagonal epath).app U q = moveClassT epath U
      (pullClassAt s hs hsb htor huS huT dualData p lieNaturality addS addT U q) := rfl

/-- The pushed-path route computes the same actual normalized pullback. -/
theorem classTowerBaseChangeAlongPath_eq
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal epath = (moveTowerS (pathPushforward b hsb htb epath)).hom ≫
      pullTowerAt t ht htb htor huS huT dualData p lieNaturality addS addT :=
  (classTowerBaseChange_pointTransport D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    b compatibility h hsb htb htor huS huT dualData p lieNaturality addS addT epath).symm

/-- The actual diagonal pullback is independent of the auxiliary path. -/
theorem classTowerBaseChangeAlongPath_path_independent
    (epath fpath : fiberFunctor s hs ≅ fiberFunctor t ht) : diagonal epath = diagonal fpath := by
  rw [classTowerBaseChangeAlongPath, classTowerBaseChangeAlongPath,
    classPointTowerIso_path_independent D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (b ≫ p) compatibility h
      htor huT addT epath fpath]

local notation "forgetSAt" => forgetCMActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p compatibility h
local notation "forgetTAt" => forgetCMActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h

/-- Forgetting polarization and level gives the existing joint CM action-class pullback. -/
theorem classTowerBaseChangeAlongPath_forgetCMAction
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal epath ≫ forgetTAt t ht htor huT addT =
      forgetSAt (s ≫ b) hsb htor huS addS ≫
        actionClassTowerBaseChange D C b p lieNaturality := by
  rw [classTowerBaseChangeAlongPath, Category.assoc,
    forgetCMActionNatTrans_classPointTowerIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (b ≫ p)
      compatibility h htor huT addT epath]
  exact classTowerBaseChange_forgetCMAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h s hs hsb htor huS huT dualData p
    lieNaturality addS addT

/-- The diagonal is natural for all original Harris inclusion and Hecke transporter arrows. -/
theorem classTowerBaseChangeAlongPath_arrow
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) {U V : Level} (f : U ⟶ V)
    (q : classesSAt (s ≫ b) hsb htor huS addS L p U) :
    (diagonal epath).app V ((towerSAt (s ≫ b) hsb htor huS addS L p).map f q) =
      (towerTAt t ht htor huT addT L (b ≫ p)).map f ((diagonal epath).app U q) :=
  (diagonal epath).naturality_apply f q

section Geometric
variable [ConnectedSpace T] [IsLocallyNoetherian T]
  [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical pullback between geometric presentations of normalized CM polarized towers. -/
def classTowerGeometricBaseChange :
    towerSAt (s ≫ b) hsb htor huS addS L p ⟶
      towerTAt t ht htor huT addT L (b ≫ p) :=
  diagonal (Classical.choice (geometricPathExists s t hs ht))

local notation "geometricPull" => classTowerGeometricBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h hsb htor huS huT dualData p
  lieNaturality addS addT (s := s) (t := t) (hs := hs) (ht := ht)
local notation "geometricMoveT" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (b ≫ p)
  compatibility h htor huT addT

/-- Every supplied path computes the canonical geometric pullback. -/
theorem classTowerGeometricBaseChange_eq_path
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricPull = diagonal epath :=
  classTowerBaseChangeAlongPath_path_independent D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h hsb htor huS huT dualData p lieNaturality
    addS addT _ epath

/-- Canonical pullback factors through pointed pullback and canonical target comparison. -/
theorem classTowerGeometricBaseChange_eq_transport :
    geometricPull = pullTowerAt s hs hsb htor huS huT dualData p lieNaturality addS addT ≫
      (geometricMoveT s t hs ht).hom := rfl

/-- The canonical geometric map retains the same actual joint CM action pullback. -/
theorem classTowerGeometricBaseChange_forgetCMAction :
    geometricPull ≫ forgetTAt t ht htor huT addT =
      forgetSAt (s ≫ b) hsb htor huS addS ≫
        actionClassTowerBaseChange D C b p lieNaturality :=
  classTowerBaseChangeAlongPath_forgetCMAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h hsb htor huS huT dualData p lieNaturality
    addS addT _

/-- Canonical geometric pullback commutes with every original Harris transporter arrow. -/
theorem classTowerGeometricBaseChange_arrow {U V : Level} (f : U ⟶ V)
    (q : classesSAt (s ≫ b) hsb htor huS addS L p U) :
    (geometricPull).app V ((towerSAt (s ≫ b) hsb htor huS addS L p).map f q) =
      (towerTAt t ht htor huT addT L (b ≫ p)).map f ((geometricPull).app U q) :=
  (geometricPull).naturality_apply f q

variable [ConnectedSpace S] [IsLocallyNoetherian S]

local notation "geometricMoveS" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h htor huS addS

/-- Canonical comparison on the source computes the alternative pullback route. -/
theorem classTowerGeometricBaseChange_eq_pushed_transport :
    geometricPull = (geometricMoveS (s ≫ b) (t ≫ b) hsb htb).hom ≫
      pullTowerAt t ht htb htor huS huT dualData p lieNaturality addS addT := by
  let epath := Classical.choice (geometricPathExists s t hs ht)
  rw [classTowerGeometricBaseChange_eq_path D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h hsb htor huS huT dualData p lieNaturality
      addS addT epath,
    classTowerBaseChangeAlongPath_eq D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      b compatibility h hsb htb htor huS huT dualData p lieNaturality addS addT epath,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h htor huS addS
      (pathPushforward b hsb htb epath)]

end Geometric
end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
