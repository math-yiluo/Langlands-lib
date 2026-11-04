import Langlands.Shimura.PEL.HarrisIntegralCMLevelClass
import Langlands.AbelianScheme.Tate.WeilPELFrame
import Mathlib.GroupTheory.Coset.Basic

/-! # Original Harris coordinates for actual integral-family monodromy -/

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

/-- Actual full Weil frames of the direct pulled integral-action family. -/
abbrev harrisIntegralCMWeilFrame :=
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) s

local notation "Frame" => harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s

local notation "rightAction" =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) s

/-- A chosen actual frame gives coordinates in the original opposite Harris group. -/
def harrisIntegralCMFrameEquiv (eta : Frame) : G ≃ Frame := by
  letI : IsSimpleRing A := D.simple
  exact (scalarEquiv).toEquiv.trans
    (Tate.weilAdelicFrameSourceEquiv P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
      (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
      (D.harrisHodgePELForm C) s
      (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
      (hodgeRationalPELConditions D C) eta)

local notation "coord" => harrisIntegralCMFrameEquiv D C P B W lam T a compatibility h s

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The coordinates retain the actual right precomposition convention. -/
theorem harrisIntegralCMFrameEquiv_apply (eta : Frame) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    coord eta g = right eta (show H from scalarEquiv g) := rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralCMFrameEquiv_one (eta : Frame) :
    coord eta 1 = eta := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  change right eta (show H from scalarEquiv 1) = eta
  rw [map_one, right_one]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Multiplication in the original group acts by actual right translation. -/
theorem harrisIntegralCMFrameEquiv_mul (eta : Frame) (g k : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    coord eta (g * k) = right (coord eta g) (show H from scalarEquiv k) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  change right eta (show H from scalarEquiv (g * k)) =
    right (right eta (show H from scalarEquiv g)) (show H from scalarEquiv k)
  rw [map_mul, right_mul]

local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).subgroup

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Equality of actual frame orbits is exactly equality of original group cosets. -/
theorem harrisIntegralCMFrameOrbit_eq_iff (eta : Frame) (U : HarrisLevel D) (g k : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    RightOrbit.mk (levelSubgroup U) (coord eta g) =
      RightOrbit.mk (levelSubgroup U) (coord eta k) ↔ g⁻¹ * k ∈ U.subgroup := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  rw [RightOrbit.mk_eq_mk]
  constructor
  · rintro ⟨u, hu, hku⟩
    let v : G := (scalarEquiv).symm u
    have hv : v ∈ U.subgroup := (hodgeLevelFunctor_obj_mem D C U v).mp (by
      simpa only [v, (scalarEquiv).apply_symm_apply] using hu)
    have hkg : k = g * v := (coord eta).injective (by
      rw [harrisIntegralCMFrameEquiv_mul]
      simpa only [v, (scalarEquiv).apply_symm_apply] using hku)
    simpa only [hkg, inv_mul_cancel_left] using hv
  · intro hgk
    refine ⟨(show H from scalarEquiv (g⁻¹ * k)),
      (hodgeLevelFunctor_obj_mem D C U _).mpr hgk, ?_⟩
    rw [← harrisIntegralCMFrameEquiv_mul]
    simp only [mul_inv_cancel_left]

/-- Original Harris cosets parametrize the actual raw frame orbits. -/
def harrisIntegralCMFrameCosetEquiv (eta : Frame) (U : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    (G ⧸ U.subgroup) ≃ RightOrbit Frame (levelSubgroup U) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  exact Quotient.congr (coord eta) (by
    intro g k
    rw [QuotientGroup.leftRel_apply]
    exact (harrisIntegralCMFrameOrbit_eq_iff
      D C P B W lam T a compatibility h s eta U g k).symm.trans
      (RightOrbit.mk_eq_mk (levelSubgroup U) (coord eta g) (coord eta k)))

local notation "cosetEquiv" => harrisIntegralCMFrameCosetEquiv
  D C P B W lam T a compatibility h s

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralCMFrameCosetEquiv_mk
    (eta : Frame) (U : HarrisLevel D) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    cosetEquiv eta U (QuotientGroup.mk g) =
      RightOrbit.mk (levelSubgroup U) (coord eta g) := rfl

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

/-- Actual geometric monodromy, expressed in the original Harris group using
the chosen frame. The action includes the actual Tate-twist transport. -/
def harrisIntegralCMFrameMonodromy (eta : Frame) : Gamma →* G := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  refine {
    toFun := fun gamma => (coord eta).symm (gamma • eta)
    map_one' := ?_
    map_mul' := ?_ }
  · apply (coord eta).injective
    rw [Equiv.apply_symm_apply, one_smul, harrisIntegralCMFrameEquiv_one]
  · intro gamma delta
    apply (coord eta).injective
    rw [Equiv.apply_symm_apply, mul_smul, harrisIntegralCMFrameEquiv_mul,
      Equiv.apply_symm_apply]
    rw [← right_comm, ← harrisIntegralCMFrameEquiv_apply, Equiv.apply_symm_apply]

local notation "rho" => harrisIntegralCMFrameMonodromy
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Monodromy becomes left multiplication in the original Harris coordinates. -/
theorem harrisIntegralCMFrameEquiv_monodromy (eta : Frame) (gamma : Gamma) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    gamma • coord eta g = coord eta (rho eta gamma * g) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  rw [harrisIntegralCMFrameEquiv_mul, harrisIntegralCMFrameEquiv_apply,
    right_comm]
  congr 1
  exact ((coord eta).apply_symm_apply (gamma • eta)).symm

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On coset representatives, actual monodromy is left multiplication by rho. -/
theorem harrisIntegralCMFrameCosetEquiv_monodromy_mk
    (eta : Frame) (U : HarrisLevel D) (gamma : Gamma) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    gamma • cosetEquiv eta U (QuotientGroup.mk g) =
      cosetEquiv eta U (QuotientGroup.mk (rho eta gamma * g)) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  rw [harrisIntegralCMFrameCosetEquiv_mk, harrisIntegralCMFrameCosetEquiv_mk,
    RightOrbit.smul_mk, harrisIntegralCMFrameEquiv_monodromy]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual left stabilizer is the conjugate subgroup membership condition. -/
theorem harrisIntegralCMFrameOrbit_stabilizer_iff
    (eta : Frame) (U : HarrisLevel D) (gamma : Gamma) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    gamma • RightOrbit.mk (levelSubgroup U) (coord eta g) =
      RightOrbit.mk (levelSubgroup U) (coord eta g) ↔
        g⁻¹ * rho eta gamma * g ∈ U.subgroup := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  rw [RightOrbit.smul_mk, harrisIntegralCMFrameEquiv_monodromy, eq_comm,
    harrisIntegralCMFrameOrbit_eq_iff, mul_assoc]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- An actual raw orbit is invariant precisely when all conjugated monodromy
coordinates belong to the original level subgroup. -/
theorem harrisIntegralCMFrameOrbit_fixed_iff
    (eta : Frame) (U : HarrisLevel D) (g : G) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) (coord eta g) ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame (levelSubgroup U)) ↔
        ∀ gamma : Gamma, g⁻¹ * rho eta gamma * g ∈ U.subgroup := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  exact forall_congr' (fun gamma => harrisIntegralCMFrameOrbit_stabilizer_iff
    D C P B W lam T a compatibility h s hs htor hu eta U gamma g)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- At the chosen frame, invariance says the monodromy homomorphism lands in U. -/
theorem harrisIntegralCMFrameOrbit_base_fixed_iff
    (eta : Frame) (U : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk (levelSubgroup U) eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame (levelSubgroup U)) ↔
        ∀ gamma : Gamma, rho eta gamma ∈ U.subgroup := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  simpa only [harrisIntegralCMFrameEquiv_one, inv_one, one_mul, mul_one] using
    (harrisIntegralCMFrameOrbit_fixed_iff
      D C P B W lam T a compatibility h s hs htor hu eta U 1)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Existence in the actual raw level tower is equivalent to the conjugated
monodromy landing in the original subgroup in some frame coordinate. -/
theorem harrisIntegralCMFullActionLevel_nonempty_iff
    (eta : Frame) (U : HarrisLevel D) :
    Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U) ↔
        ∃ g : G, ∀ gamma : Gamma, g⁻¹ * rho eta gamma * g ∈ U.subgroup := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  change Nonempty (InvariantOrbit (X := Frame) Gamma (levelSubgroup U)) ↔ _
  constructor
  · rintro ⟨q⟩
    obtain ⟨xi, hxi⟩ := Quotient.exists_rep q.val
    refine ⟨(coord eta).symm xi, (harrisIntegralCMFrameOrbit_fixed_iff
      D C P B W lam T a compatibility h s hs htor hu eta U _).mp ?_⟩
    simpa only [Equiv.apply_symm_apply, RightOrbit.mk, hxi] using q.property
  · rintro ⟨g, hg⟩
    exact ⟨⟨RightOrbit.mk (levelSubgroup U) (coord eta g),
      (harrisIntegralCMFrameOrbit_fixed_iff
        D C P B W lam T a compatibility h s hs htor hu eta U g).mpr hg⟩⟩

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
