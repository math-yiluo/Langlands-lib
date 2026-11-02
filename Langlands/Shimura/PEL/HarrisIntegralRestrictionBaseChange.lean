import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange
import Langlands.Shimura.PEL.PolarizedWeilIntegralClasses
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationBaseChange

/-! # Supplied integral data on actual Harris pointed pullback -/

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


local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "IntegralMult" => PolarizedWeilLevel.IntegralPolarizedMultiple preservation
  composition unitCoherence associativity comparison symmetry stability square universality

/-- Pull back a supplied integral restriction on the same actual Harris representative. -/
def levelDataIntegralRestrictionBaseChange {U : HarrisLevel D} (x : DataS U)
    (a : letI := auxiliaryStarRing D C; Restriction O x.1) :
    letI := auxiliaryStarRing D C; Restriction O (pullData U x).1 := by
  letI := auxiliaryStarRing D C
  refine
    { action := baseChangeOrderAction b x.1.actionObj.abelianScheme a.action
      agrees := ?_ }
  intro z
  change homToHom0 ((Langlands.AbelianScheme.baseChange b).map (a.action z)) =
    rationalBaseChangeHom b (x.1.actionObj.action (z : A))
  exact (rationalBaseChangeHom_ofHom b (a.action z)).symm.trans
    (congrArg (rationalBaseChangeHom b) (a.agrees z))

local notation "pullRestriction" => levelDataIntegralRestrictionBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

set_option maxHeartbeats 2400000 in
/-- Transport the supplied exactly equivariant integral representative of the same
rational action isomorphism; its two denominators and actual maps are retained. -/
def levelDataIntegralIsoBaseChange {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (a : Restriction O x.1) (a' : Restriction O y.1)
    (e : x.1.actionObj ≅ y.1.actionObj)
    (_d : EquivariantRationalIsoIntegralData a.action a'.action
      (RationalAlgebraAction.underlyingIso e)),
    EquivariantRationalIsoIntegralData (S := T)
      (B := (Langlands.AbelianScheme.baseChange b).obj x.1.actionObj.abelianScheme)
      (C := (Langlands.AbelianScheme.baseChange b).obj y.1.actionObj.abelianScheme)
      (pullRestriction x a).action (pullRestriction y a').action
      (RationalAlgebraAction.underlyingIso ((RationalAlgebraAction.pullback b).mapIso e)) := by
  letI := auxiliaryStarRing D C
  intro a a' e d
  exact d.baseChange b

local notation "pullIsoData" => levelDataIntegralIsoBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- Transport the supplied exact integral polarization witnesses along the same
actual pointed pullback and the same mapped rational action isomorphism. -/
def levelDataIntegralPolarizationBaseChange {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (a : Restriction O x.1) (a' : Restriction O y.1)
    (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
    (d : EquivariantRationalIsoIntegralData a.action a'.action
      (RationalAlgebraAction.underlyingIso e))
    (_hd : Rationalization.IntegralMultipleData
      (integralDualPullbackHom preservation composition unitCoherence associativity comparison
        symmetry stability x.1.hasDual y.1.hasDual x.1.geometry y.1.geometry
        x.1.inversePoincare x.1.evaluation y.1.inversePoincare y.1.evaluation
        d.hom y.1.polarization) x.1.polarization
      (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * (q : ℚ))),
    Rationalization.IntegralMultipleData
      (integralDualPullbackHom preservation composition unitCoherence associativity comparison
        symmetry stability (pullData U x).1.hasDual (pullData U y).1.hasDual
        (pullData U x).1.geometry (pullData U y).1.geometry
        (pullData U x).1.inversePoincare (pullData U x).1.evaluation
        (pullData U y).1.inversePoincare (pullData U y).1.evaluation
        (pullIsoData x y a a' e d).hom (pullData U y).1.polarization)
      (pullData U x).1.polarization
      ((((pullIsoData x y a a' e d).homDenom : ℚ) *
        ((pullIsoData x y a a' e d).homDenom : ℚ)) * (q : ℚ)) := by
  letI := auxiliaryStarRing D C
  intro a a' q e d hd
  exact integralDualMultipleDataBaseChange preservation stability composition unitCoherence
    associativity comparison symmetry universality dualAbelianBaseChange b
    x.1.actionObj.abelianScheme y.1.actionObj.abelianScheme
    x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
    y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
    (dualData x.1).hasDual (dualData x.1).geometry
    (dualData x.1).inversePoincare (dualData x.1).evaluation
    (dualData y.1).hasDual (dualData y.1).geometry
    (dualData y.1).inversePoincare (dualData y.1).evaluation
    (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * (q : ℚ))
    d.hom x.1.polarization y.1.polarization hd

/-- Exact integral action and polarization witnesses survive actual Harris pullback,
with the original multiplier and the image of the original rational isomorphism. -/
theorem levelDataIntegralPolarizedMultiple_baseChange {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (a : Restriction O x.1) (a' : Restriction O y.1)
    (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj),
    IntegralMult x.1 y.1 a a' q e →
      IntegralMult (pullData U x).1 (pullData U y).1
        (pullRestriction x a) (pullRestriction y a') q
        ((RationalAlgebraAction.pullback b).mapIso e) := by
  let := auxiliaryStarRing D C
  intro a a' q e
  rintro ⟨d, ⟨hd⟩⟩
  refine ⟨pullIsoData x y a a' e d, ⟨?_⟩⟩
  exact levelDataIntegralPolarizationBaseChange D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData x y a a' q e d hd

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
