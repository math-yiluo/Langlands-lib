import Langlands.Shimura.PEL.HarrisIntegralCMLevelFiniteOrbits
import Langlands.AbelianScheme.Tate.AdelicScalarTopology

/-! # Continuous actual Harris monodromy from an invariant compact open level -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

attribute [local instance] Tate.rationalTopology

open NumberField _root_.Algebra

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
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)
    (T : Over S) [QuasiSeparatedSpace T.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "H" =>
  ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

local notation "Frame" => harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s
local notation "coord" => harrisIntegralCMFrameEquiv D C P B W lam T a compatibility h s
local notation "R" => Global.FiniteAdeles ℚ
local notation "Source" => R ⊗[ℚ] A
local notation "Target" => Tate.RationalFull BT (Over.mk s)
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).subgroup
local notation "RawOrbits" U => RightOrbit Frame (levelSubgroup U)
local notation "rightAction" =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) s

/-- The underlying actual full frame is linear over the finite adeles. -/
def harrisIntegralCMFrameScalarLinear (eta : Frame) :
    letI := GroupScheme.Tate.finiteAdeleModule (BT).toGrp (Over.mk s) (fun _ => True) h
    Source →ₗ[R] Target := by
  letI := scalarExtensionAlgebraModule A A R
  letI := Tate.finiteAdeleAlgebraModule BT (Over.mk s) (fun _ => True) h iT
  letI := GroupScheme.Tate.finiteAdeleModule (BT).toGrp (Over.mk s) (fun _ => True) h
  refine {
    toFun := eta.1
    map_add' := eta.1.map_add
    map_smul' := ?_ }
  intro r x
  rw [← scalarExtensionAlgebraModule_one_tmul_smul A A R r x, eta.1.map_smul]
  change Tate.finiteAdeleAlgebraAction BT (Over.mk s) (fun _ => True) h iT
    ((1 : A) ⊗ₜ[ℚ] r) (eta.1 x) = _
  rw [Tate.finiteAdeleAlgebraAction_tmul, map_one, map_one]
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Only the forward continuity of the actual full frame is used. -/
theorem continuous_harrisIntegralCMFrame (eta : Frame) :
    letI : TopologicalSpace Source := moduleTopology R Source
    Continuous (fun x : Source => eta.1 x) := by
  let : TopologicalSpace Source := moduleTopology R Source
  let : Module R Target :=
    GroupScheme.Tate.finiteAdeleModule (BT).toGrp (Over.mk s) (fun _ => True) h
  let : IsTopologicalAddGroup Target := Tate.rationalFull_topologicalAddGroup BT (Over.mk s)
  let : ContinuousSMul R Target := Tate.finiteAdeleModule_continuousSMul BT (Over.mk s) h
  exact IsModuleTopology.continuous_of_linearMap
    (harrisIntegralCMFrameScalarLinear D C P B W lam T a compatibility h s eta)

/-- Pointwise evaluation of actual Harris frame coordinates. -/
def harrisIntegralCMFrameEvaluation (eta : Frame) (g : G) (x : Source) : Target :=
  (coord eta g).1 x

local notation "evaluation" => harrisIntegralCMFrameEvaluation
  D C P B W lam T a compatibility h s

omit [IsCMField F] [IsScalarTower ℚ F A] in
theorem harrisIntegralCMFrameEvaluation_injective (eta : Frame) :
    Function.Injective (evaluation eta) := by
  intro g k hgk
  apply (coord eta).injective
  apply Subtype.ext
  apply LinearEquiv.ext
  exact congrFun hgk

omit [IsCMField F] [IsScalarTower ℚ F A] in
theorem continuous_harrisIntegralCMFrameEvaluation (eta : Frame) :
    Continuous (evaluation eta) := by
  let : TopologicalSpace Source := moduleTopology R Source
  apply continuous_pi
  intro x
  change Continuous (fun g : G => eta.1 ((show H from scalarEquiv g).val.1 x))
  exact (continuous_harrisIntegralCMFrame
    D C P B W lam T a compatibility h s eta).comp
      ((ScalarExtensionSimilitudePoints.continuous_apply x).comp
        (scalarEquiv).continuous)

variable
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs

local notation "monodromyAction" =>
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    s hs htor hu

local notation "actionsComm" =>
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    s hs htor hu

local notation "rho" => harrisIntegralCMFrameMonodromy
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- An invariant raw orbit at compact open U bounds the actual monodromy in U.
Compact frame evaluation then recovers continuity from actual Tate monodromy. -/
theorem continuous_harrisIntegralCMFrameMonodromy_of_fixed
    (eta : Frame) (U : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) eta ∈
      MulAction.fixedPoints Gamma (RawOrbits U) → Continuous (rho eta) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : T2Space Target := Tate.rationalFull_t2Space BT (Over.mk s)
  let : CompactSpace U.subgroup := isCompact_iff_compactSpace.mp U.isCompact
  intro heta
  have hrange : ∀ gamma : Gamma, rho eta gamma ∈ U.subgroup :=
    (harrisIntegralCMFrameOrbit_base_fixed_iff
      D C P B W lam T a compatibility h s hs htor hu eta U).mp heta
  let f : Gamma → U.subgroup := fun gamma => ⟨rho eta gamma, hrange gamma⟩
  let ev : U.subgroup → (Source → Target) := fun u => evaluation eta u.val
  have hev : Topology.IsEmbedding ev :=
    ((continuous_harrisIntegralCMFrameEvaluation
      D C P B W lam T a compatibility h s eta).comp continuous_subtype_val).isClosedEmbedding
        ((harrisIntegralCMFrameEvaluation_injective
          D C P B W lam T a compatibility h s eta).comp Subtype.val_injective) |>.isEmbedding
  have hmon : Continuous (ev ∘ f) := by
    apply continuous_pi
    intro x
    have hc := (Tate.continuous_rationalFullMonodromy BT s hs htor hu).comp
      (continuous_id.prodMk (continuous_const (y := eta.1 x)))
    apply hc.congr
    intro gamma
    have hcoord : coord eta (rho eta gamma) = gamma • eta :=
      (coord eta).apply_symm_apply (gamma • eta)
    exact (congrArg (fun xi : Frame => xi.1 x) hcoord).symm
  exact continuous_subtype_val.comp (hev.continuous_iff.mpr hmon)

/-- The actual original-group monodromy as a continuous homomorphism, using
one invariant raw orbit at the chosen compact open level. -/
def harrisIntegralCMContinuousFrameMonodromy
    (eta : Frame) (U : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) eta ∈
      MulAction.fixedPoints Gamma (RawOrbits U) → (Gamma →ₜ* G) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta
  exact {
    toMonoidHom := rho eta
    continuous_toFun := continuous_harrisIntegralCMFrameMonodromy_of_fixed
      D C P B W lam T a compatibility h s hs htor hu eta U heta }

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
