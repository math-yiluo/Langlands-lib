import Langlands.Shimura.PEL.HarrisTaylorLiePolarizedBaseChange
import Langlands.Shimura.PEL.HarrisTaylorLiePointTransport
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelPathBaseChange

/-! # Mixed point and base pullback of actual Harris polarized Lie classes -/

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

local notation "Level" => HarrisLevel D
local notation "dataAt" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "pullRepAt" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualAbelianBaseChangeNaturality
  polarizationBaseChange b compatibility h
local notation "moveRepS" => pointMapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS
local notation "moveRepT" => pointMapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huT

/-- Actual polarized pullback commutes with the pushed path, using the same dual inputs. -/
theorem levelDataBaseChange_pointMapRepresentative
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (x : dataAt (s ≫ b) hsb htor huS U) :
    pullRepAt t ht htb htor huS huT dualData U
        (moveRepS (pathPushforward b hsb htb epath) U x) =
      moveRepT epath U (pullRepAt s hs hsb htor huS huT dualData U x) := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact Langlands.AbelianScheme.Tate.weilAdelicLevelBaseChange_transport b
    x.1.actionObj.abelianScheme preservation composition unitCoherence associativity
    comparison symmetry stability universality x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation W.hasDual W.geometry W.inversePoincare W.evaluation
    compatibility x.1.polarization h x.1.actionObj.action A (D.harrisHodgePELForm C)
    htor hsb htb huS huT ((hodgeLevelFunctor D C).obj U).toSubgroup epath x.2

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "ambientAt" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
local notation "pullAmbientAt" => ambientClassBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h
local notation "moveAmbientS" => ambientPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS addS
local notation "moveAmbientT" => ambientPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huT addT

/-- The mixed square descends to the existing actual polarized rational-isogeny quotient. -/
theorem ambientClassBaseChange_pointMap
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : ambientAt (s ≫ b) hsb htor huS addS U) :
    pullAmbientAt t ht htb htor huS huT dualData addS addT U
        ((moveAmbientS (pathPushforward b hsb htb epath)).hom.app U q) =
      (moveAmbientT epath).hom.app U
        (pullAmbientAt s hs hsb htor huS huT dualData addS addT U q) := by
  let := auxiliaryStarRing D C
  refine Quotient.inductionOn q ?_
  intro x
  exact congrArg (Quotient.mk _) (levelDataBaseChange_pointMapRepresentative D C
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality b compatibility h hsb htb htor huS huT dualData epath U x)

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F] (p : S ⟶ Spec (.of F))

local notation "classesAt" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "pullClassAt" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
local notation "moveClassS" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h htor huS addS
local notation "moveClassT" => classPointMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h htor huT addT
local notation "moveTowerS" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h htor huS addS
local notation "moveTowerT" => classPointTowerIso D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h htor huT addT
local notation "pullTowerAt" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
local notation "towerSAt" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "towerTAt" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p) compatibility h

/-- The same-representative dimension and positive Lie restriction retains the mixed square. -/
theorem classBaseChange_pointMap
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesAt (s ≫ b) hsb htor huS addS U) :
    pullClassAt t ht htb htor huS huT dualData L p addS addT U
        (moveClassS (pathPushforward b hsb htb epath) U q) =
      moveClassT epath U
        (pullClassAt s hs hsb htor huS huT dualData L p addS addT U q) := by
  apply Subtype.ext
  exact ambientClassBaseChange_pointMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    hsb htb htor huS huT dualData addS addT epath U q.val

/-- Pointed pullback and actual point comparison commute as maps of original Harris towers. -/
theorem classTowerBaseChange_pointTransport
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (moveTowerS (pathPushforward b hsb htb epath)).hom ≫
        pullTowerAt t ht htb htor huS huT dualData L p addS addT =
      pullTowerAt s hs hsb htor huS huT dualData L p addS addT ≫ (moveTowerT epath).hom := by
  ext U q
  exact classBaseChange_pointMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality b compatibility h hsb htb htor huS huT
    dualData addS addT L p epath U q

/-- Diagonal pullback of actual polarized dimension-and-Lie classes, natural in original levels. -/
def classTowerBaseChangeAlongPath (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    towerSAt (s ≫ b) hsb htor huS addS ⟶ towerTAt t ht htor huT addT :=
  pullTowerAt s hs hsb htor huS huT dualData L p addS addT ≫ (moveTowerT epath).hom

local notation "diagonal" => classTowerBaseChangeAlongPath D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality b compatibility h
  hsb htor huS huT dualData addS addT L p

/-- Every diagonal component is the actual pointed pullback followed by point comparison. -/
@[simp] theorem classTowerBaseChangeAlongPath_app
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) (U : Level)
    (q : classesAt (s ≫ b) hsb htor huS addS U) :
    (diagonal epath).app U q = moveClassT epath U
      (pullClassAt s hs hsb htor huS huT dualData L p addS addT U q) := rfl

/-- The alternative route transports along the pushed path before pointed pullback. -/
theorem classTowerBaseChangeAlongPath_eq
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal epath = (moveTowerS (pathPushforward b hsb htb epath)).hom ≫
      pullTowerAt t ht htb htor huS huT dualData L p addS addT :=
  (classTowerBaseChange_pointTransport D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality b compatibility h hsb htb htor huS huT
    dualData addS addT L p epath).symm

/-- The entire diagonal pullback is independent of the auxiliary path. -/
theorem classTowerBaseChangeAlongPath_path_independent
    (epath fpath : fiberFunctor s hs ≅ fiberFunctor t ht) : diagonal epath = diagonal fpath := by
  rw [classTowerBaseChangeAlongPath, classTowerBaseChangeAlongPath,
    classPointTowerIso_path_independent D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L (b ≫ p) compatibility h
      htor huT addT epath fpath]

local notation "includeSAt" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h
local notation "includeTAt" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p) compatibility h
local notation "pullAmbientTowerAt" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h
local notation "forgetSAt" => forgetDimensionLieActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p compatibility h
local notation "forgetTAt" => forgetDimensionLieActionNatTrans D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h

/-- The diagonal restricts the same ambient polarized quotient construction. -/
theorem classTowerBaseChangeAlongPath_inclusion
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal epath ≫ includeTAt t ht htor huT addT =
      includeSAt (s ≫ b) hsb htor huS addS ≫
        pullAmbientTowerAt s hs hsb htor huS huT dualData addS addT ≫
          (moveAmbientT epath).hom := by
  ext U q
  rfl

/-- The underlying joint action-class pullback is independent of the endpoint presentation. -/
theorem classTowerBaseChangeAlongPath_forgetDimensionLieAction
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal epath ≫ forgetTAt t ht htor huT addT =
      forgetSAt (s ≫ b) hsb htor huS addS ≫ actionClassTowerBaseChange D b L p := by
  rw [classTowerBaseChangeAlongPath, Category.assoc,
    forgetDimensionLieActionNatTrans_classPointTowerIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)
      compatibility h htor huT addT epath]
  exact classTowerBaseChange_forgetDimensionLieAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs hsb htor huS huT dualData L p addS addT

/-- Naturality includes every original Harris inclusion and both Hecke transporter legs. -/
theorem classTowerBaseChangeAlongPath_arrow
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) {U V : Level} (f : U ⟶ V)
    (q : classesAt (s ≫ b) hsb htor huS addS U) :
    (diagonal epath).app V ((towerSAt (s ≫ b) hsb htor huS addS).map f q) =
      (towerTAt t ht htor huT addT).map f ((diagonal epath).app U q) :=
  (diagonal epath).naturality_apply f q

section Geometric
variable [ConnectedSpace T] [IsLocallyNoetherian T]
  [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical pullback between geometric-point presentations of the actual Harris class towers. -/
def classTowerGeometricBaseChange :
    towerSAt (s ≫ b) hsb htor huS addS ⟶ towerTAt t ht htor huT addT :=
  diagonal (Classical.choice (geometricPathExists s t hs ht))

local notation "geometricPull" => classTowerGeometricBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality b compatibility h
  hsb htor huS huT dualData addS addT L p
  (s := s) (t := t) (hs := hs) (ht := ht)
local notation "geometricMoveT" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h htor huT addT

/-- Every supplied path computes the canonical pullback of the entire tower. -/
theorem classTowerGeometricBaseChange_eq_path
    (epath : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricPull = diagonal epath :=
  classTowerBaseChangeAlongPath_path_independent D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h hsb htor
    huS huT dualData addS addT L p _ epath

/-- Canonical pullback uses pointed pullback and canonical comparison on the target base. -/
theorem classTowerGeometricBaseChange_eq_transport :
    geometricPull =
      pullTowerAt s hs hsb htor huS huT dualData L p addS addT ≫
        (geometricMoveT s t hs ht).hom := rfl

/-- Canonical geometric pullback restricts the constructed ambient polarized diagonal. -/
theorem classTowerGeometricBaseChange_inclusion :
    geometricPull ≫ includeTAt t ht htor huT addT =
      includeSAt (s ≫ b) hsb htor huS addS ≫
        pullAmbientTowerAt s hs hsb htor huS huT dualData addS addT ≫
          (moveAmbientT (Classical.choice (geometricPathExists s t hs ht))).hom :=
  classTowerBaseChangeAlongPath_inclusion D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h hsb htor
    huS huT dualData addS addT L p _

/-- Canonical geometric pullback agrees with the existing joint action presheaf map. -/
theorem classTowerGeometricBaseChange_forgetDimensionLieAction :
    geometricPull ≫ forgetTAt t ht htor huT addT =
      forgetSAt (s ≫ b) hsb htor huS addS ≫ actionClassTowerBaseChange D b L p :=
  classTowerBaseChangeAlongPath_forgetDimensionLieAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b compatibility h
    hsb htor huS huT dualData addS addT L p _

/-- Canonical pullback commutes with all original Harris level transporters. -/
theorem classTowerGeometricBaseChange_arrow {U V : Level} (f : U ⟶ V)
    (q : classesAt (s ≫ b) hsb htor huS addS U) :
    (geometricPull).app V ((towerSAt (s ≫ b) hsb htor huS addS).map f q) =
      (towerTAt t ht htor huT addT).map f ((geometricPull).app U q) :=
  (geometricPull).naturality_apply f q

variable [ConnectedSpace S] [IsLocallyNoetherian S]

local notation "geometricMoveS" => classGeometricPointTowerIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h htor huS addS

/-- On geometric bases, canonical comparison on the source gives the same pullback route. -/
theorem classTowerGeometricBaseChange_eq_pushed_transport :
    geometricPull =
      (geometricMoveS (s ≫ b) (t ≫ b) hsb htb).hom ≫
        pullTowerAt t ht htb htor huS huT dualData L p addS addT := by
  let epath := Classical.choice (geometricPathExists s t hs ht)
  rw [classTowerGeometricBaseChange_eq_path D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h hsb htor
      huS huT dualData addS addT L p epath,
    classTowerBaseChangeAlongPath_eq D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h hsb htb htor huS huT
      dualData addS addT L p epath,
    classGeometricPointTowerIso_eq_path D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h htor huS addS
      (pathPushforward b hsb htb epath)]

end Geometric
end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
