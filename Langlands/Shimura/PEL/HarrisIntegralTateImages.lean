import Langlands.Shimura.PEL.HarrisPolarizedWeilClasses
import Langlands.Shimura.PEL.HarrisIntegralPairing
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.Global.IntegralFiniteAdeles

/-! # Integral Tate images from normalized Harris Weil frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The integral finite-adele span of the existing integer Harris pairing lattice. -/
def harrisHodgePELIntegralAdeleSpan :
    letI : Module (Global.integralFiniteAdeles ℚ)
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) :=
      Module.compHom _ (Global.integralFiniteAdeles ℚ).subtype
    Submodule (Global.integralFiniteAdeles ℚ)
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) := by
  letI : Module (Global.integralFiniteAdeles ℚ)
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) :=
    Module.compHom _ (Global.integralFiniteAdeles ℚ).subtype
  exact Submodule.span (Global.integralFiniteAdeles ℚ)
    (Set.range (fun x : D.harrisHodgePELIntegralLattice C =>
      (1 : Global.FiniteAdeles ℚ) ⊗ₜ[ℚ] (x : A)))

theorem harrisHodgePELIntegralAdeleSpan_tmul
    (x : D.harrisHodgePELIntegralLattice C) :
    (1 : Global.FiniteAdeles ℚ) ⊗ₜ[ℚ] (x : A) ∈
      D.harrisHodgePELIntegralAdeleSpan C :=
  Submodule.subset_span ⟨x, rfl⟩

end Langlands.Shimura.CentralSimpleUnitaryData

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

/-- Source similitudes preserving the actual integral finite-adele span in both directions. -/
def harrisIntegralAdeleStabilizer : Subgroup G where
  carrier := {g | ∀ v : Vf, g.1.1 v ∈ Λf ↔ v ∈ Λf}
  one_mem' := by intro v; rfl
  mul_mem' {g k} hg hk := by
    intro v
    change g.1.1 (k.1.1 v) ∈ Λf ↔ v ∈ Λf
    exact (hg (k.1.1 v)).trans (hk v)
  inv_mem' {g} hg := by
    intro v
    change g.1.1.symm v ∈ Λf ↔ v ∈ Λf
    have hv := hg (g.1.1.symm v)
    simpa only [LinearEquiv.apply_symm_apply] using hv.symm

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

/-- Normalization identifies this fixed source span with the full actual integral Tate image. -/
def HarrisIntegralFrameCondition (X : PObj) (eta : Frame X) : Prop :=
  letI := auxiliaryStarRing D C
  ∀ v : Vf, v ∈ Λf ↔
    ∃ x : GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s),
      GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s)
        (fun _ => True) x = eta.1 v

local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s

omit [IsScalarTower ℚ F A] in
/-- The original opposite right action preserves normalization at a stabilizing similitude. -/
theorem harrisIntegralFrameCondition_right (X : PObj) (eta : Frame X)
    (g : G) (hg : g ∈ harrisIntegralAdeleStabilizer D C) :
    letI := auxiliaryStarRing D C
    letI := rightAction X
    Normalized X (right eta g) ↔ Normalized X eta := by
  let := auxiliaryStarRing D C
  let := rightAction X
  constructor
  · intro hn v
    have hv := hn (g.1.1.symm v)
    change g.1.1.symm v ∈ Λf ↔
      ∃ x : GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s),
        GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) x = eta.1 (g.1.1 (g.1.1.symm v)) at hv
    rw [LinearEquiv.apply_symm_apply] at hv
    have hg' : v ∈ Λf ↔ g.1.1.symm v ∈ Λf := by
      simpa only [LinearEquiv.apply_symm_apply] using hg (g.1.1.symm v)
    exact hg'.trans hv
  · intro hn v
    change v ∈ Λf ↔
      ∃ x : GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s),
        GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) x = eta.1 (g.1.1 v)
    exact (hg v).symm.trans (hn (g.1.1 v))


omit [IsScalarTower ℚ F A] in
/-- Equal original right orbits have the same normalization at an integral stabilizing level. -/
theorem harrisIntegralFrameCondition_of_orbit_eq (X : PObj)
    (eta xi : Frame X) (U : Subgroup G)
    (hU : U ≤ harrisIntegralAdeleStabilizer D C) :
    letI := rightAction X
    RightOrbit.mk U eta = RightOrbit.mk U xi →
      (Normalized X eta ↔ Normalized X xi) := by
  let := rightAction X
  intro heq
  obtain ⟨g, hg, rfl⟩ := (RightOrbit.mk_eq_mk U eta xi).mp heq
  exact (harrisIntegralFrameCondition_right D C P compatibility h s X eta g (hU hg)).symm

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

/-- An original geometrically fixed level orbit contains an integral-normalized frame. -/
def HarrisIntegralLevelCondition (X : PObj) (K : Level) (x : (tower X).obj K) : Prop :=
  letI := rightAction X
  ∃ eta : Frame X, Normalized X eta ∧ RightOrbit.mk K.toSubgroup eta = x.1

local notation "LevelNormalized" =>
  HarrisIntegralLevelCondition D C P compatibility h s hs htor hu

omit [IsScalarTower ℚ F A] in
/-- At a stabilizing level, normalization holds for every representative exactly when
it holds for one representative of the original fixed orbit. -/
theorem harrisIntegralLevelCondition_iff (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) (eta : Frame X) :
    letI := rightAction X
    RightOrbit.mk K.toSubgroup eta = x.1 →
      (LevelNormalized X K x ↔ Normalized X eta) := by
  let := rightAction X
  intro heta
  constructor
  · rintro ⟨xi, hxi, hclass⟩
    exact (harrisIntegralFrameCondition_of_orbit_eq D C P compatibility h s X xi eta
      K.toSubgroup hK (hclass.trans heta.symm)).mp hxi
  · intro hn
    exact ⟨eta, hn, heta⟩

variable (additivity : PositivePairAdditivity D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S))

local notation "Mult" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality additivity
local notation "transport" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelIso P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity

omit [IsScalarTower ℚ F A] in
/-- Equality of original normalized fixed level orbits forces both actual rational
isogeny arrows to preserve the full integral Tate image. -/
theorem harrisIntegralLevelCondition_integralImages (X Y : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
    (x : (tower X).obj K) (y : (tower Y).obj K)
    (_ : LevelNormalized X K x) (_ : LevelNormalized Y K y),
    transport X Y K q e he x = y →
    (∀ a : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
      ∃ b : GroupScheme.Tate.Full Y.actionObj.abelianScheme.toGrp (Over.mk s),
        Tate.rationalHomMap (Over.mk s) (fun _ => True)
          (RationalAlgebraAction.underlyingIso e).hom
          (GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
            (Over.mk s) (fun _ => True) a) =
          GroupScheme.Tate.toRational Y.actionObj.abelianScheme.toGrp
            (Over.mk s) (fun _ => True) b) ∧
    (∀ b : GroupScheme.Tate.Full Y.actionObj.abelianScheme.toGrp (Over.mk s),
      ∃ a : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        Tate.rationalHomMap (Over.mk s) (fun _ => True)
          (RationalAlgebraAction.underlyingIso e).inv
          (GroupScheme.Tate.toRational Y.actionObj.abelianScheme.toGrp
            (Over.mk s) (fun _ => True) b) =
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
            (Over.mk s) (fun _ => True) a) := by
  let := auxiliaryStarRing D C
  intro e he x y hx hy heq
  let := rightAction X
  let := rightAction Y
  obtain ⟨eta, hneta, heta⟩ := hx
  obtain ⟨xi, hnxi, hxi⟩ := hy
  let f : Frame X ≃ Frame Y := Tate.weilAdelicFrameIsogeny P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    X.hasDual Y.hasDual X.geometry Y.geometry X.inversePoincare X.evaluation
    Y.inversePoincare Y.evaluation (additivity X Y) X.polarization Y.polarization
    compatibility rationalWeilFunctoriality h X.actionObj.action Y.actionObj.action
    A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom) he
  have hf : ∀ eta (g : G), f (right eta g) = right (f eta) g :=
    Tate.weilAdelicFrameIsogeny_right P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      X.hasDual Y.hasDual X.geometry Y.geometry X.inversePoincare X.evaluation
      Y.inversePoincare Y.evaluation (additivity X Y) X.polarization Y.polarization
      compatibility rationalWeilFunctoriality h X.actionObj.action Y.actionObj.action
      A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
      (RationalAlgebraAction.intertwines e.hom) he
  have horbit := congrArg Subtype.val heq
  change RightOrbit.map K.toSubgroup f hf x.1 = y.1 at horbit
  rw [← heta, ← hxi, RightOrbit.map_mk] at horbit
  have hnfe : Normalized Y (f eta) :=
    (harrisIntegralFrameCondition_of_orbit_eq D C P compatibility h s Y
      (f eta) xi K.toSubgroup hK horbit).mpr hnxi
  have hf_apply (v : Vf) :
      (f eta).1 v = Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom (eta.1 v) := rfl
  let r := Tate.rationalIso (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.underlyingIso e)
  constructor
  · intro a
    let v := eta.1.symm (GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp
      (Over.mk s) (fun _ => True) a)
    have hv : v ∈ Λf := (hneta v).mpr ⟨a, (eta.1.apply_symm_apply _).symm⟩
    obtain ⟨b, hb⟩ := (hnfe v).mp hv
    refine ⟨b, ?_⟩
    rw [hf_apply] at hb
    simpa only [v, LinearEquiv.apply_symm_apply] using hb.symm
  · intro b
    let v := (f eta).1.symm (GroupScheme.Tate.toRational Y.actionObj.abelianScheme.toGrp
      (Over.mk s) (fun _ => True) b)
    have hv : v ∈ Λf := (hnfe v).mpr ⟨b, ((f eta).1.apply_symm_apply _).symm⟩
    obtain ⟨a, ha⟩ := (hneta v).mp hv
    refine ⟨a, ?_⟩
    apply r.injective
    change r (r.symm _) = r _
    rw [LinearEquiv.apply_symm_apply, ha]
    change _ = (f eta).1 v
    exact ((f eta).1.apply_symm_apply _).symm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
