import Langlands.Shimura.PEL.HarrisIntegralCMLevelContinuousMonodromy
import Mathlib.CategoryTheory.Galois.ContAction

/-! # Finite continuous actual Harris monodromy orbits -/

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
local notation "cosetEquiv" => harrisIntegralCMFrameCosetEquiv
  D C P B W lam T a compatibility h s
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).subgroup
local notation "RawOrbits" U => RightOrbit Frame (levelSubgroup U)
local notation "rightAction" =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) s

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
/-- One invariant compact-level orbit makes every raw stabilizer open. -/
theorem harrisIntegralCMFrameOrbit_stabilizer_isOpen_of_fixed
    (eta : Frame) (U V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) eta ∈
      MulAction.fixedPoints Gamma (RawOrbits U) →
    ∀ q : RawOrbits V, IsOpen (MulAction.stabilizer Gamma q : Set Gamma) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  let : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  intro heta q
  have hr : Continuous (rho eta) := continuous_harrisIntegralCMFrameMonodromy_of_fixed
    D C P B W lam T a compatibility h s hs htor hu eta U heta
  obtain ⟨xi, rfl⟩ := Quotient.exists_rep q
  let g : G := (coord eta).symm xi
  have hc : Continuous (fun gamma : Gamma => g⁻¹ * rho eta gamma * g) :=
    (continuous_const.mul hr).mul continuous_const
  have heq : (MulAction.stabilizer Gamma (RightOrbit.mk (levelSubgroup V) xi) : Set Gamma) =
      (fun gamma : Gamma => g⁻¹ * rho eta gamma * g) ⁻¹' (V.subgroup : Set G) := by
    ext gamma
    change gamma • RightOrbit.mk (levelSubgroup V) xi =
      RightOrbit.mk (levelSubgroup V) xi ↔
        g⁻¹ * rho eta gamma * g ∈ V.subgroup
    simpa only [g, Equiv.apply_symm_apply] using
      (harrisIntegralCMFrameOrbit_stabilizer_iff
        D C P B W lam T a compatibility h s hs htor hu eta V gamma g)
  exact heq.symm ▸ V.openSubgroup.isOpen.preimage hc

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- A value of the unchanged raw tower supplies the invariant representative. -/
theorem harrisIntegralCMFrameOrbit_stabilizer_isOpen_of_level_nonempty
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, IsOpen (MulAction.stabilizer Gamma q : Set Gamma) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  change Nonempty (InvariantOrbit (X := Frame) Gamma (levelSubgroup U)) at hU
  obtain ⟨qU⟩ := hU
  obtain ⟨eta, heta⟩ := Quotient.exists_rep qU.val
  apply harrisIntegralCMFrameOrbit_stabilizer_isOpen_of_fixed
    D C P B W lam T a compatibility h s hs htor hu eta U V
  simpa only [RightOrbit.mk, heta] using qU.property

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual raw action at every level is continuous for the discrete topology. -/
theorem harrisIntegralCMRawContinuousSMul_of_level_nonempty
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    letI : TopologicalSpace (RawOrbits V) := ⊥
    ContinuousSMul Gamma (RawOrbits V) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : TopologicalSpace (RawOrbits V) := ⊥
  let : DiscreteTopology (RawOrbits V) := ⟨rfl⟩
  exact continuousSMul_iff_stabilizer_isOpen.mpr
    (harrisIntegralCMFrameOrbit_stabilizer_isOpen_of_level_nonempty
      D C P B W lam T a compatibility h s hs htor hu U V hU)

open scoped FintypeCatDiscrete

/-- Each actual raw monodromy orbit, with its actual finite continuous action. -/
def harrisIntegralCMFiniteOrbitAction
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    (RawOrbits V) → ContAction FintypeCat.{0} Gamma := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  letI : Fintype (MulAction.orbit Gamma q) :=
    (harrisIntegralCMFrameOrbit_finite_of_level_nonempty
      D C P B W lam T a compatibility h s hs htor hu U V hU q).fintype
  let : TopologicalSpace (MulAction.orbit Gamma q) := ⊥
  let : DiscreteTopology (MulAction.orbit Gamma q) := ⟨rfl⟩
  refine ⟨Action.FintypeCat.ofMulAction Gamma (FintypeCat.of (MulAction.orbit Gamma q)), ?_⟩
  change ContinuousSMul Gamma (MulAction.orbit Gamma q)
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro r
  have heq : (MulAction.stabilizer Gamma r : Set Gamma) =
      (MulAction.stabilizer Gamma r.val : Set Gamma) := by
    ext gamma
    exact Subtype.ext_iff
  rw [heq]
  exact harrisIntegralCMFrameOrbit_stabilizer_isOpen_of_level_nonempty
    D C P B W lam T a compatibility h s hs htor hu U V hU r.val

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
