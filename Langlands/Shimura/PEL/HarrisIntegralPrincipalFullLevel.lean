import Langlands.Shimura.PEL.HarrisIntegralOrderedFullLevel

/-! # Ordered markings at principal Harris levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

private theorem fullLevel_eq_of_sections {S : Scheme.{0}} {B : AbelianScheme S} {g m : ℕ}
    (v w : FullLevel B g m) (hvw : v.sections = w.sections) : v = w := by
  cases v
  cases w
  cases hvw
  rfl

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (h : Global.RationalProfiniteIntegerAdeleComparison)

local notation "gH" => Module.finrank ℚ E * n ^ 2
local notation "HodgeGroup" =>
  ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "Residue" => HarrisIntegralSourceMod D C

/-- The source residue coordinates in the ordering used by
`harrisIntegralOrderedFullLevel`. -/
def harrisPrincipalSourceCoordinates (m : Index (fun _ => True)) :
    (Fin (2 * gH) → ZMod m.val) ≃+ Residue m.val := by
  let ixs : Fin (2 * gH) ≃ Fin (Module.finrank ℤ (D.harrisHodgePELIntegralLattice C)) :=
    finCongr (harrisIntegralSource_rank D C).symm
  let reindex : (Fin (2 * gH) → ZMod m.val) ≃+
      (Fin (Module.finrank ℤ (D.harrisHodgePELIntegralLattice C)) → ZMod m.val) :=
    { toFun := fun f i => f (ixs.symm i)
      invFun := fun f i => f (ixs i)
      left_inv := fun f => funext fun i => congrArg f (ixs.symm_apply_apply i)
      right_inv := fun f => funext fun i => congrArg f (ixs.apply_symm_apply i)
      map_add' := fun _ _ => rfl }
  exact reindex.trans
    (harrisIntegralReducedSourceCoordinates D C h ⟨m.val, m.property.1⟩).symm

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation compatibility (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation "red" => harrisIntegralFrameReduction D C P compatibility h s
local notation "source" => harrisPrincipalSourceCoordinates D C h

variable [IsAlgClosed Ω]

/-- An ordered marking is compatible with the Harris data at `s` if a normalized
Weil frame lifts its coordinates over `s`. -/
def HarrisPrincipalFullLevelCondition (X : PObj) (m : Index (fun _ => True))
    (v : FullLevel (BOf X) gH m.val) : Prop :=
  ∃ (eta : Frame X) (hn : Normalized X eta),
    ∀ a, red X m eta hn (source m a) = v.fibreCoordinates Ω s a

variable [ConnectedSpace S] [IsLocallyNoetherian S]
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation:max "RAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation compatibility (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation:max "LAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility rationalWeilGeometricTransport
    (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
local notation:max "CommAct" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility rationalWeilGeometricTransport
    (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation:max "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality compatibility h A
    (D.harrisHodgePELForm C) s hs htor hu X
local notation "LevelNormalized" => HarrisIntegralLevelCondition D C P compatibility h s hs htor hu
local notation "ord" => harrisIntegralOrderedFullLevel D C P compatibility h s hs htor hu
local notation "LiftCondition" => HarrisPrincipalFullLevelCondition D C h P compatibility s

/-- In source residue coordinates, restriction of the ordered marking to the
reference point is reduction of any normalized frame representing the orbit. -/
theorem harrisIntegralOrderedFullLevel_fibreCoordinates (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val)
    (x : (tower X).obj U) (hx : LevelNormalized X U x) (eta : Frame X) (hn : Normalized X eta) :
    letI : MulAction HodgeGroupᵐᵒᵖ (Frame X) := RAct X
    RightOrbit.mk U.toSubgroup eta = x.1 →
      ∀ a, (ord X m U hU x hx).fibreCoordinates Ω s a = red X m eta hn (source m a) := by
  let _ : MulAction HodgeGroupᵐᵒᵖ (Frame X) := RAct X
  intro he a
  let f := (ord X m U hU x hx).fibreCoordinates Ω s
  let r := (red X m eta hn).comp (source m).toAddMonoidHom
  let rLinear : (Fin (2 * gH) → ZMod m.val) →ₗ[ZMod m.val]
      GroupScheme.Tate.Level (BOf X).toGrp (Over.mk s) m.val :=
    { r with map_smul' := ZMod.map_smul r }
  have hf : f.toLinearMap = rLinear := by
    apply (Pi.basisFun (ZMod m.val) (Fin (2 * gH))).ext
    intro i
    rw [Pi.basisFun_apply]
    change (ord X m U hU x hx).fibreCoordinates Ω s (Pi.single i 1) = _
    rw [FullLevel.fibreCoordinates_single]
    change GroupScheme.Tate.levelRestrict (BOf X).toGrp (Over.homMk s (by simp)) m.val
      (harrisIntegralLevelSections D C P s hs htor hu compatibility h X m U hU x hx
        (source m (Pi.single i 1))) = red X m eta hn (source m (Pi.single i 1))
    rw [harrisIntegralLevelSections_restrict]
    exact harrisIntegralLevelReduction_apply D C P compatibility h s hs htor hu
      X m U hU x hx eta hn he _
  exact DFunLike.congr_fun hf a

omit [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] [QuasiSeparatedSpace S] hμfin hμet in
private theorem fibreCoordinates_fixed (X : PObj) (m : Index (fun _ => True))
    (v : FullLevel (BOf X) gH m.val) (a : Fin (2 * gH) → ZMod m.val) :
    v.fibreCoordinates Ω s a ∈ harrisIntegralFixedTorsion D C P s hs htor hu X m := by
  let atPoint : Over.mk s ⟶ Over.mk (𝟙 S) := Over.homMk s (by simp)
  let r := GroupScheme.Tate.levelRestrict (BOf X).toGrp atPoint m.val
  let eval : GroupScheme.Tate.Level (BOf X).toGrp (Over.mk (𝟙 S)) m.val →ₗ[ZMod m.val]
      GroupScheme.Tate.Level (BOf X).toGrp (Over.mk s) m.val :=
    { r with map_smul' := ZMod.map_smul r }
  let z : GroupScheme.Tate.Level (BOf X).toGrp (Over.mk (𝟙 S)) m.val :=
    ∑ i, a i • v.sections i
  have hz : v.fibreCoordinates Ω s a = eval z := by
    rw [FullLevel.fibreCoordinates_apply]
    dsimp only [z]
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hz]
  exact (harrisIntegralGlobalTorsionEquiv D C P s hs htor hu X m z).property

/-- At the principal congruence subgroup, the original normalized invariant
level orbits classify precisely the full finite markings admitting a normalized
geometric lift. -/
def harrisPrincipalFullLevelEquiv (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup = Cong m.val) :
    {x : (tower X).obj U // LevelNormalized X U x} ≃
      {v : FullLevel (BOf X) gH m.val // LiftCondition X m v} := by
  let _ : MulAction HodgeGroupᵐᵒᵖ (Frame X) := RAct X
  let _ : MulAction (FundamentalGroup s hs) (Frame X) := LAct X
  let _ : SMulCommClass (FundamentalGroup s hs) HodgeGroupᵐᵒᵖ (Frame X) := CommAct X
  let forward (x : {x : (tower X).obj U // LevelNormalized X U x}) :
      {v : FullLevel (BOf X) gH m.val // LiftCondition X m v} := by
    refine ⟨ord X m U hU.le x.1 x.2, ?_⟩
    obtain ⟨eta, hn, he⟩ := x.2
    exact ⟨eta, hn, fun a => (harrisIntegralOrderedFullLevel_fibreCoordinates
      D C h P compatibility s hs htor hu X m U hU.le x.1 x.2 eta hn he a).symm⟩
  apply Equiv.ofBijective forward
  constructor
  · intro x y hxy
    have hv := congrArg Subtype.val hxy
    obtain ⟨eta, hn, he⟩ := x.2
    obtain ⟨xi, hx, he'⟩ := y.2
    have hr : red X m eta hn = red X m xi hx := by
      apply AddMonoidHom.ext
      intro q
      obtain ⟨a, rfl⟩ := (source m).surjective q
      rw [← harrisIntegralOrderedFullLevel_fibreCoordinates D C h P compatibility
        s hs htor hu X m U hU.le x.1 x.2 eta hn he,
        ← harrisIntegralOrderedFullLevel_fibreCoordinates D C h P compatibility
          s hs htor hu X m U hU.le y.1 y.2 xi hx he']
      change (forward x).1.fibreCoordinates Ω s a = (forward y).1.fibreCoordinates Ω s a
      rw [hv]
    have horb := (harrisIntegralFrameReduction_eq_iff_rightOrbit D C P compatibility h s hu
      X m eta xi hn hx).mp hr
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨g, hg, hge⟩ := (RightOrbit.mk_eq_mk (Cong m.val) eta xi).mp horb
    have horb' := (RightOrbit.mk_eq_mk U.toSubgroup eta xi).mpr ⟨g, hU.symm ▸ hg, hge⟩
    exact he.symm.trans (horb'.trans he')
  · rintro ⟨v, eta, hn, hv⟩
    have hfix : ∀ (gamma : FundamentalGroup s hs) q,
        Tate.levelMonodromy s hs htor (BOf X) m.val m.property.1 (hu m) gamma
          (red X m eta hn q) = red X m eta hn q := by
      intro gamma q
      obtain ⟨a, rfl⟩ := (source m).surjective q
      rw [hv]
      exact fibreCoordinates_fixed D C P s hs htor hu X m v a gamma
    have hfixed := (harrisIntegralFrameReduction_fixed_iff D C P compatibility h s hs htor hu
      X m eta hn).mpr hfix
    have hfixedU := (RightOrbit.mk_mem_fixedPoints (G := HodgeGroup)
      (Γ := FundamentalGroup s hs) (X := Frame X) U.toSubgroup eta).mpr (by
      intro gamma
      obtain ⟨g, hg, hge⟩ := (RightOrbit.mk_mem_fixedPoints (G := HodgeGroup)
        (Γ := FundamentalGroup s hs) (X := Frame X) (Cong m.val) eta).mp hfixed gamma
      exact ⟨g, hU.symm ▸ hg, hge⟩)
    let x : (tower X).obj U := ⟨RightOrbit.mk U.toSubgroup eta, hfixedU⟩
    have hx : LevelNormalized X U x := ⟨eta, hn, rfl⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    apply fullLevel_eq_of_sections
    have he : RightOrbit.mk U.toSubgroup eta = x.1 := rfl
    funext i
    apply (harrisIntegralGlobalTorsionEquiv D C P s hs htor hu X m).injective
    apply Subtype.ext
    change fibreTuple (ord X m U hU.le x hx).sections s i = fibreTuple v.sections s i
    rw [← FullLevel.fibreCoordinates_single, ← FullLevel.fibreCoordinates_single,
      harrisIntegralOrderedFullLevel_fibreCoordinates D C h P compatibility s hs htor hu
        X m U hU.le x hx eta hn he, hv]

@[simp] theorem harrisPrincipalFullLevelEquiv_apply_val
    (X : PObj) (m : Index (fun _ => True)) (U : ULevel) (hU : U.toSubgroup = Cong m.val)
    (x : {x : (tower X).obj U // LevelNormalized X U x}) :
    (harrisPrincipalFullLevelEquiv D C h P compatibility s hs htor hu X m U hU x).val =
      ord X m U hU.le x.val x.property := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
