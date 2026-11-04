import Langlands.Shimura.PEL.HarrisIntegralCMLevelMonodromy
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Finite actual monodromy orbits from an invariant Harris level -/

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

private theorem compactOpen_cosetImage_finite
    {J : Type*} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (U V : CompactOpenLevel J) (g : J) :
    ((fun u : J => (QuotientGroup.mk (u * g) : J ⧸ V.subgroup)) ''
      (U.subgroup : Set J)).Finite := by
  let : DiscreteTopology (J ⧸ V.subgroup) :=
    QuotientGroup.discreteTopology V.openSubgroup.isOpen
  exact (U.isCompact.image (QuotientGroup.continuous_mk.comp
    (continuous_id.mul continuous_const))).finite_of_discrete

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
/-- One invariant orbit at a compact open level makes every raw orbit at any
other compact open level finite under actual monodromy. -/
theorem harrisIntegralCMFrameOrbit_finite_of_fixed
    (eta : Frame) (U V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) eta ∈
      MulAction.fixedPoints Gamma (RawOrbits U) →
    ∀ q : RawOrbits V, (MulAction.orbit Gamma q).Finite := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  let : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  intro heta q
  have hrange : ∀ gamma : Gamma, rho eta gamma ∈ U.subgroup :=
    (harrisIntegralCMFrameOrbit_base_fixed_iff
      D C P B W lam T a compatibility h s hs htor hu eta U).mp heta
  obtain ⟨xi, rfl⟩ := Quotient.exists_rep q
  let g : G := (coord eta).symm xi
  apply ((compactOpen_cosetImage_finite U V g).image (cosetEquiv eta V)).subset
  rintro _ ⟨gamma, rfl⟩
  refine ⟨QuotientGroup.mk (rho eta gamma * g),
    ⟨rho eta gamma, hrange gamma, rfl⟩, ?_⟩
  simpa only [harrisIntegralCMFrameCosetEquiv_mk, g,
    Equiv.apply_symm_apply, RightOrbit.mk] using
    (harrisIntegralCMFrameCosetEquiv_monodromy_mk
      D C P B W lam T a compatibility h s hs htor hu eta V gamma g).symm

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- A nonempty value of the existing raw integral-action tower supplies the
invariant representative needed for finite orbits at every level. -/
theorem harrisIntegralCMFrameOrbit_finite_of_level_nonempty
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, (MulAction.orbit Gamma q).Finite := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  change Nonempty (InvariantOrbit (X := Frame) Gamma (levelSubgroup U)) at hU
  obtain ⟨qU⟩ := hU
  obtain ⟨eta, heta⟩ := Quotient.exists_rep qU.val
  apply harrisIntegralCMFrameOrbit_finite_of_fixed
    D C P B W lam T a compatibility h s hs htor hu eta U V
  simpa only [RightOrbit.mk, heta] using qU.property

/-- The actual finite monodromy orbit of a raw frame-orbit class, enumerated
using nonemptiness at one compact open level of the unchanged raw tower. -/
def harrisIntegralCMFrameMonodromyOrbitFinset
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    (RawOrbits V) → Finset (RawOrbits V) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  exact fun q => (harrisIntegralCMFrameOrbit_finite_of_level_nonempty
    D C P B W lam T a compatibility h s hs htor hu U V hU q).toFinset

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem mem_harrisIntegralCMFrameMonodromyOrbitFinset
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q r : RawOrbits V,
      r ∈ harrisIntegralCMFrameMonodromyOrbitFinset
        D C P B W lam T a compatibility h s hs htor hu U V hU q ↔
      ∃ gamma : Gamma, gamma • q = r := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r
  exact Set.Finite.mem_toFinset _

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
