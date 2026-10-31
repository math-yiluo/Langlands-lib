import Langlands.Shimura.PEL.HarrisPolarizedTowerBaseChange
import Langlands.AlgebraicGeometry.Picard.RationalDualPullbackBaseChange
import Langlands.AbelianScheme.Tate.WeilBaseChangeIsogeny

/-! # Pointed pullback of actual Harris polarized isogeny classes -/

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

/-- Constrained construction inputs for the actual dual of a specified abelian
scheme. No polarized action or level is an output field of this bundle. -/
structure DualEvaluationData
    (preservation : pullbackTensorComparisonIsIsoStatement.{0})
    (stability : PicardZeroPullbackStatement.{0})
    {T : Scheme.{0}} (B : AbelianScheme T) where
  hasDual : HasDualScheme B
  geometry : DualSchemeGeometry B hasDual
  inversePoincare : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hasDual))
  evaluation : tensorObj (poincareFamily B hasDual).obj.carrier inversePoincare.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hasDual))
  dualEndAdditivity : DualSchemeMapAdditivity preservation stability B B hasDual hasDual

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
  {S T : Scheme.{0}} (b : T ⟶ S)

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

/-- The dual inputs are indexed by the actual pullback of the same source
abelian scheme; no independent changed abelian scheme can be supplied. -/
def PositivePullbackDualData (X : PObjS) : Type 1 :=
  letI := auxiliaryStarRing D C
  DualEvaluationData preservation stability
    ((Langlands.AbelianScheme.baseChange b).obj X.actionObj.abelianScheme)

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

include dualityNaturality polarizationStability dualData in
/-- Pull back the actual polarized action and its actual fixed level orbit.
The source orbit supplies the frame used to prove faithfulness. -/
def levelDataBaseChange (U : HarrisLevel D) (x : DataS U) : DataT U := by
  letI : StarRing A := auxiliaryStarRing D C
  let W := dualData x.1
  let frameExists := level_nonempty_adelicFrame D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    t hs htor huS x.1 U x.2
  exact ⟨framedPositiveActionBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b x.1 W.hasDual W.geometry W.inversePoincare W.evaluation
      W.dualEndAdditivity h t frameExists,
    (framedPositiveActionTowerBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT x.1
      W.hasDual W.geometry W.inversePoincare W.evaluation W.dualEndAdditivity
      frameExists).app U x.2⟩

local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "relS" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS
local notation "relT" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) t ht htor huT addT

set_option maxHeartbeats 2400000 in
/-- The same actual rational-isogeny relation survives pullback. The changed
geometric multiplier is proved from integral dual naturality. -/
theorem levelDataBaseChange_related {U : HarrisLevel D} {x y : DataS U} :
    letI := auxiliaryStarRing D C
    (relS ((indexFunctor).obj U)).r x y →
      (relT ((indexFunctor).obj U)).r (pullData U x) (pullData U y) := by
  let := auxiliaryStarRing D C
  rintro ⟨q, e, he, hxy⟩
  let Wx := dualData x.1
  let Wy := dualData y.1
  let xb := pullData U x
  let yb := pullData U y
  let eb : xb.1.actionObj ≅ yb.1.actionObj := (RationalAlgebraAction.pullback b).mapIso e
  have hcanonical := IsRationalDualPullbackMultiple.integral_baseChange_of_naturality
      preservation stability composition unitCoherence associativity comparison symmetry
      universality dualAbelianBaseChange b x.1.actionObj.abelianScheme y.1.actionObj.abelianScheme
      x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
      y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
      Wx.hasDual Wx.geometry Wx.inversePoincare Wx.evaluation
      Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation
      (addS x.1 y.1) (addT xb.1 yb.1) dualityNaturality (q : ℚ)
      (RationalAlgebraAction.underlyingIso e).hom x.1.polarization y.1.polarization he
  have heb : PolarizedWeilLevel.Multiple preservation composition unitCoherence
      associativity comparison symmetry stability square universality addT xb.1 yb.1 q eb :=
    hcanonical
  refine ⟨q, eb, heb, ?_⟩
  have squareAt := Tate.weilAdelicLevelIsogeny_baseChange
    (A := x.1.actionObj.abelianScheme) (B := y.1.actionObj.abelianScheme) (D := A)
    b preservation composition
    unitCoherence associativity comparison symmetry stability universality
    x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation x.1.polarization
    y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation y.1.polarization
    Wx.hasDual Wx.geometry Wx.inversePoincare Wx.evaluation
    Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation
    (addS x.1 y.1) (addT xb.1 yb.1) compatibility h
    x.1.actionObj.action y.1.actionObj.action A (D.harrisHodgePELForm C) t
    (hμfin := hμfinS) (hμet := hμetS) (hμfinb := hμfinT) (hμetb := hμetT)
  have squareFor := squareAt q (RationalAlgebraAction.underlyingIso e)
  have squareIntertwines := squareFor (RationalAlgebraAction.intertwines e.hom)
  have squareSource := squareIntertwines he
  have hsquare := squareSource
    (by simpa only [canonicalDualValuedBaseChange, rationalBaseChangeIso_hom, homToHom0]
      using hcanonical) ht hs htor huS huT
    ((indexFunctor).obj U).toSubgroup x.2
  have hxyb := congrArg
    (Tate.weilAdelicLevelBaseChange b y.1.actionObj.abelianScheme preservation composition
      unitCoherence associativity comparison symmetry stability universality
      y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
      Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation compatibility
      y.1.polarization h y.1.actionObj.action A (D.harrisHodgePELForm C) t
      ht hs htor huS huT ((indexFunctor).obj U).toSubgroup) hxy
  have composed := hsquare.symm.trans hxyb
  exact composed

/-- Pullback on ambient polarized-isogeny classes, descended from actual
representatives with their original Harris level. -/
def ambientClassBaseChange (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    Quotient (relS ((indexFunctor).obj U)) → Quotient (relT ((indexFunctor).obj U)) := by
  let := auxiliaryStarRing D C
  exact Quotient.map (pullData U) (fun _ _ hxy =>
    levelDataBaseChange_related D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      b compatibility h t ht hs htor huS huT dualData addS addT hxy)

local notation "pullClass" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData addS addT

@[simp] theorem ambientClassBaseChange_mk (U : HarrisLevel D) (x : DataS U) :
    letI := auxiliaryStarRing D C
    pullClass U (Quotient.mk _ x) = Quotient.mk _ (pullData U x) := rfl

local notation "mapS" => PolarizedWeilLevel.mapData preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS
local notation "mapT" => PolarizedWeilLevel.mapData preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  A (D.harrisHodgePELForm C) t ht htor huT

/-- The actual representative pullback commutes with every original Harris
transporter; its faithfulness witnesses agree by proof irrelevance. -/
theorem levelDataBaseChange_mapData {U V : HarrisLevel D} (f : U ⟶ V) (x : DataS U) :
    letI := auxiliaryStarRing D C
    pullData V (mapS ((indexFunctor).map f) x) =
      mapT ((indexFunctor).map f) (pullData U x) := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  let frameExists := level_nonempty_adelicFrame D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    t hs htor huS x.1 U x.2
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact NatTrans.naturality_apply
    (framedPositiveActionTowerBaseChange D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT x.1
      W.hasDual W.geometry W.inversePoincare W.evaluation W.dualEndAdditivity frameExists)
    f x.2

local notation "ambientTowerS" => (hodgeLevelFunctor D C) ⋙
  PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS
local notation "ambientTowerT" => (hodgeLevelFunctor D C) ⋙
  PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) t ht htor huT addT

/-- Pointed pullback is natural on the ambient polarized-isogeny class towers
reindexed by the original Harris compact-open transporter category. -/
def ambientClassTowerBaseChange :
    letI := auxiliaryStarRing D C
    ambientTowerS ⟶ ambientTowerT := by
  let := auxiliaryStarRing D C
  refine { app := fun U => ↾(pullClass U), naturality := ?_ }
  intro U V f
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  change Quotient.mk _ (pullData V (mapS ((indexFunctor).map f) x)) =
    Quotient.mk _ (mapT ((indexFunctor).map f) (pullData U x))
  exact congrArg (Quotient.mk _) (levelDataBaseChange_mapData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData f x)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
