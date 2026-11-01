import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange

/-! # Independence of actual Harris polarized pullback from dual-evaluation choices -/

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
  {S T : Scheme.{0}} (b : T ⟶ S)

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

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

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "DataT" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT
local notation "indexFunctor" => hodgeLevelFunctor D C

local notation "pull₁" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₁
local notation "pull₂" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₂

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
/-- The rational-isogeny relation survives pullback with independently supplied
actual dual-evaluation families at its two endpoints. -/
theorem levelDataBaseChange_related_of_dualData {U : HarrisLevel D} {x y : DataS U} :
    letI := auxiliaryStarRing D C
    (relS ((indexFunctor).obj U)).r x y →
      (relT ((indexFunctor).obj U)).r (pull₁ U x) (pull₂ U y) := by
  let := auxiliaryStarRing D C
  rintro ⟨q, e, he, hxy⟩
  let Wx := dualData₁ x.1
  let Wy := dualData₂ y.1
  let xb := pull₁ U x
  let yb := pull₂ U y
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

local notation "pullClass₁" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₁ addS addT
local notation "pullClass₂" => ambientClassBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData₂ addS addT

/-- Arbitrary actual dual-evaluation families induce the identical ambient
polarized class pullback. -/
theorem ambientClassBaseChange_dualData (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    pullClass₁ U = pullClass₂ U := by
  let := auxiliaryStarRing D C
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  exact levelDataBaseChange_related_of_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData₁ dualData₂
    addS addT ((relS ((indexFunctor).obj U)).refl x)

local notation "pullTower₁" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
  dualData₁ addS addT
local notation "pullTower₂" => ambientClassTowerBaseChange D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
  dualData₂ addS addT

/-- Independence holds as equality of natural transformations on the original
Harris transporter category, including all level and Hecke maps. -/
theorem ambientClassTowerBaseChange_dualData :
    letI := auxiliaryStarRing D C
    pullTower₁ = pullTower₂ := by
  let := auxiliaryStarRing D C
  ext U q
  exact congrFun (ambientClassBaseChange_dualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
    dualData₁ dualData₂ addS addT U) q

local notation "ambientTowerS" => (hodgeLevelFunctor D C) ⋙
  PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS
local notation "ambientTowerT" => (hodgeLevelFunctor D C) ⋙
  PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) t ht htor huT addT

/-- Canonical ambient class pullback from existence of actual dual inputs.
The resulting tower map is independent of every choice made here. -/
def ambientClassTowerBaseChangeOfExists
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X)) :
    letI := auxiliaryStarRing D C
    ambientTowerS ⟶ ambientTowerT := by
  let := auxiliaryStarRing D C
  exact ambientClassTowerBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) addS addT

/-- Every actual family computes the canonical map constructed from existence. -/
theorem ambientClassTowerBaseChangeOfExists_eq
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X)) :
    letI := auxiliaryStarRing D C
    ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht hs htor huS huT addS addT dualExists =
      pullTower₁ := by
  let := auxiliaryStarRing D C
  exact ambientClassTowerBaseChange_dualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) dualData₁ addS addT

/-- Canonical ambient pullback acts on each quotient class by any actual family. -/
@[simp] theorem ambientClassTowerBaseChangeOfExists_app
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X))
    (U : HarrisLevel D)
    (q : letI := auxiliaryStarRing D C; (ambientTowerS).obj U) :
    letI := auxiliaryStarRing D C
    (ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT addS addT dualExists).app U q =
      pullClass₁ U q := by
  let := auxiliaryStarRing D C
  exact congrArg (fun (towerMap : ambientTowerS ⟶ ambientTowerT) => towerMap.app U q)
    (ambientClassTowerBaseChangeOfExists_eq D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h t ht hs htor huS huT dualData₁
      addS addT dualExists)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
