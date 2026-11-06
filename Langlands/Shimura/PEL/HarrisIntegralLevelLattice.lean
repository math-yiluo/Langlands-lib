import Langlands.Shimura.PEL.HarrisIntegralTateImages
import Langlands.AbelianScheme.Tate.WeilAdelicLevelTransport

/-! # The integral lattice carried by an original Harris level orbit -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Vf" => (Global.FiniteAdeles ℚ) ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "adelicModule" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.finiteAdeleModule (X).actionObj.abelianScheme.toGrp
    (Over.mk s) (fun _ => True) h
local notation "integralModule" X:max =>
  letI := auxiliaryStarRing D C
  letI := adelicModule X
  Module.compHom (Rat X) (Rf).subtype

private theorem source_scalar (a : Af) (v : Vf) :
    letI := scalarExtensionAlgebraModule A A Af
    ((1 : A) ⊗ₜ[ℚ] a) • v = a • v := by
  let := scalarExtensionAlgebraModule A A Af
  induction v using TensorProduct.inductionOn with
  | tmul r x =>
    rw [scalarExtensionAlgebraModule_tmul_smul]
    simp only [one_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, hx, hy]

omit [IsScalarTower ℚ F A] [QuasiSeparatedSpace S] in
private theorem target_scalar (X : PObj) (a : Af) (w : Rat X) :
    letI := auxiliaryStarRing D C
    letI := Tate.finiteAdeleAlgebraModule X.actionObj.abelianScheme (Over.mk s)
      (fun _ => True) h X.actionObj.action
    letI := adelicModule X
    ((1 : A) ⊗ₜ[ℚ] a) • w = a • w := by
  let := auxiliaryStarRing D C
  let := Tate.finiteAdeleAlgebraModule X.actionObj.abelianScheme (Over.mk s)
    (fun _ => True) h X.actionObj.action
  let := adelicModule X
  change Tate.rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
    (X.actionObj.action 1) (Tate.finiteAdeleAction X.actionObj.abelianScheme
      (Over.mk s) (fun _ => True) h a w) = _
  rw [map_one, map_one]
  rfl

private def frameIntegralLinearMap (X : PObj) (eta : Frame X) :
    letI : Module Rf Vf := Module.compHom _ (Rf).subtype
    letI := integralModule X
    Vf →ₗ[Rf] Rat X := by
  let := auxiliaryStarRing D C
  letI : Module Rf Vf := Module.compHom _ (Rf).subtype
  letI := integralModule X
  refine { eta.1.toAddMonoidHom with map_smul' := ?_ }
  intro a v
  have he := eta.1.map_smul (((1 : A) ⊗ₜ[ℚ] (a : Af))) v
  rw [source_scalar, target_scalar D C P h s X] at he
  exact he

/-- The actual image of the fixed Harris integral finite-adele span under a
compatible frame, as an integral finite-adele submodule of the rational Tate space. -/
def harrisIntegralFrameLattice (X : PObj) (eta : Frame X) :
    letI := integralModule X
    Submodule Rf (Rat X) := by
  letI := integralModule X
  exact (Λf).map (frameIntegralLinearMap D C P compatibility h s X eta)

local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] in
/-- Membership is literal membership in the transported source span. -/
theorem mem_harrisIntegralFrameLattice (X : PObj) (eta : Frame X) (w : Rat X) :
    w ∈ lattice X eta ↔ ∃ v : Vf, v ∈ Λf ∧ eta.1 v = w := Iff.rfl

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralFrameLattice_apply_mem (X : PObj) (eta : Frame X) (v : Vf) :
    eta.1 v ∈ lattice X eta ↔ v ∈ Λf := by
  rw [mem_harrisIntegralFrameLattice]
  constructor
  · rintro ⟨w, hw, he⟩
    exact eta.1.injective he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [IsScalarTower ℚ F A] in
/-- Integral source stabilizers do not change the transported lattice. -/
theorem harrisIntegralFrameLattice_right (X : PObj) (eta : Frame X)
    (g : G) (hg : g ∈ harrisIntegralAdeleStabilizer D C) :
    letI := rightAction X
    lattice X (right eta g) = lattice X eta := by
  let := rightAction X
  let := integralModule X
  ext w
  rw [mem_harrisIntegralFrameLattice, mem_harrisIntegralFrameLattice]
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨g.1.1 v, (hg v).mpr hv, he⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨g.1.1.symm v, ?_, ?_⟩
    · exact (hg (g.1.1.symm v)).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using hv)
    · change eta.1 (g.1.1 (g.1.1.symm v)) = eta.1 v
      rw [LinearEquiv.apply_symm_apply]

omit [IsScalarTower ℚ F A] in
/-- Equal original frame orbits carry equal lattices at an integral stabilizing level. -/
theorem harrisIntegralFrameLattice_of_orbit_eq (X : PObj)
    (eta xi : Frame X) (U : Subgroup G)
    (hU : U ≤ harrisIntegralAdeleStabilizer D C) :
    letI := rightAction X
    RightOrbit.mk U eta = RightOrbit.mk U xi →
      lattice X eta = lattice X xi := by
  let := rightAction X
  intro he
  obtain ⟨g, hg, rfl⟩ := (RightOrbit.mk_eq_mk U eta xi).mp he
  exact (harrisIntegralFrameLattice_right D C P compatibility h s X eta g (hU hg)).symm

/-- The lattice descends to the original right orbit, without choosing a frame. -/
def harrisIntegralOrbitLattice (X : PObj) (U : Subgroup G)
    (hU : U ≤ harrisIntegralAdeleStabilizer D C) :
    letI := rightAction X
    letI := integralModule X
    RightOrbit (Frame X) U → Submodule Rf (Rat X) := by
  let := rightAction X
  letI := integralModule X
  refine Quotient.lift (lattice X) ?_
  rintro eta xi ⟨g, hg, rfl⟩
  exact (harrisIntegralFrameLattice_right D C P compatibility h s X eta g (hU hg)).symm

local notation "orbitLattice" =>
  harrisIntegralOrbitLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralOrbitLattice_mk (X : PObj) (U : Subgroup G)
    (hU : U ≤ harrisIntegralAdeleStabilizer D C) (eta : Frame X) :
    letI := rightAction X
    orbitLattice X U hU (RightOrbit.mk U eta) = lattice X eta := rfl

omit [IsScalarTower ℚ F A] in
/-- Normalization is precisely equality with the full integral Tate rationalization image. -/
theorem harrisIntegralFrameCondition_iff_lattice (X : PObj) (eta : Frame X) :
    letI := auxiliaryStarRing D C
    HarrisIntegralFrameCondition D C P compatibility h s X eta ↔
      (lattice X eta : Set (Rat X)) =
        Set.range (GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
          (Over.mk s) (fun _ => True)) := by
  let := auxiliaryStarRing D C
  constructor
  · intro hn
    ext w
    obtain ⟨v, rfl⟩ := eta.1.surjective w
    exact (harrisIntegralFrameLattice_apply_mem D C P compatibility h s X eta v).trans (hn v)
  · intro he v
    rw [← harrisIntegralFrameLattice_apply_mem D C P compatibility h s X eta v]
    change eta.1 v ∈ (lattice X eta : Set (Rat X)) ↔ _
    rw [he]
    rfl

variable
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "leftAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s hs htor hu
local notation "actionsComm" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s hs htor hu

/-- The lattice carried by an original geometrically fixed Harris level orbit. -/
def harrisIntegralLevelLattice (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := integralModule X
    Submodule Rf (Rat X) :=
  orbitLattice X K.toSubgroup hK x.1

local notation "levelLattice" =>
  harrisIntegralLevelLattice D C P compatibility h s hs htor hu

omit [IsScalarTower ℚ F A] in
/-- Evaluating at any representative recovers its transported source span. -/
theorem harrisIntegralLevelLattice_eq_frame (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) (eta : Frame X) :
    letI := rightAction X
    RightOrbit.mk K.toSubgroup eta = x.1 →
      levelLattice X K hK x = lattice X eta := by
  let := rightAction X
  intro he
  change orbitLattice X K.toSubgroup hK x.1 = _
  rw [← he]
  rfl

omit [IsScalarTower ℚ F A] in
/-- Orbit fixedness forces the carried lattice to be invariant under actual
rational Tate monodromy; the representative frame need not be fixed. -/
theorem harrisIntegralLevelLattice_monodromy (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) (gamma : FundamentalGroup s hs) (w : Rat X) :
    letI := auxiliaryStarRing D C
    Tate.rationalMonodromy s hs htor X.actionObj.abelianScheme (fun _ => True) hu
      gamma w ∈ levelLattice X K hK x ↔ w ∈ levelLattice X K hK x := by
  let := auxiliaryStarRing D C
  let := rightAction X
  let := leftAction X
  let := actionsComm X
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have hfixed : RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints (FundamentalGroup s hs) (RightOrbit (Frame X) K.toSubgroup) := by
    change (⟦eta⟧ : RightOrbit (Frame X) K.toSubgroup) ∈ _
    rw [heta]
    exact x.2
  obtain ⟨g, hg, he⟩ := (RightOrbit.mk_mem_fixedPoints K.toSubgroup eta).mp hfixed gamma
  have hlat := harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
    X K hK x eta heta
  rw [hlat]
  obtain ⟨v, rfl⟩ := eta.1.surjective w
  have hev := congrArg (fun xi : Frame X => xi.1 v) he
  change Tate.rationalMonodromy s hs htor X.actionObj.abelianScheme (fun _ => True) hu
    gamma (eta.1 v) = eta.1 (g.1.1 v) at hev
  rw [hev, harrisIntegralFrameLattice_apply_mem, harrisIntegralFrameLattice_apply_mem]
  exact hK hg v

omit [IsScalarTower ℚ F A] in
/-- At an integral stabilizing level, the original existential normalization
condition is equality of the orbit's lattice with the full integral Tate image. -/
theorem harrisIntegralLevelCondition_iff_lattice (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := auxiliaryStarRing D C
    HarrisIntegralLevelCondition D C P compatibility h s hs htor hu X K x ↔
      (levelLattice X K hK x : Set (Rat X)) =
        Set.range (GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
          (Over.mk s) (fun _ => True)) := by
  let := auxiliaryStarRing D C
  let := rightAction X
  constructor
  · rintro ⟨eta, hn, heta⟩
    rw [harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
      X K hK x eta heta]
    exact (harrisIntegralFrameCondition_iff_lattice D C P compatibility h s X eta).mp hn
  · intro he
    obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
    refine ⟨eta, ?_, heta⟩
    apply (harrisIntegralFrameCondition_iff_lattice D C P compatibility h s X eta).mpr
    rw [← harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
      X K hK x eta heta]
    exact he

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
