import Langlands.Shimura.PEL.HarrisIntegralLevelLattice

/-! # Carried Harris lattices under original rational-isogeny transport -/

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

local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "integralModule" X:max =>
  letI := auxiliaryStarRing D C
  letI := Tate.finiteAdeleModule (X).actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  Module.compHom (Rat X) (Rf).subtype
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s

variable (additivity : PositivePairAdditivity D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S))

local notation "Mult" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality additivity
local notation "frameIso" X:max Y:max q:max e:max he:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameIsogeny P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    (X).hasDual (Y).hasDual (X).geometry (Y).geometry (X).inversePoincare (X).evaluation
    (Y).inversePoincare (Y).evaluation (additivity X Y) (X).polarization (Y).polarization
    compatibility rationalWeilFunctoriality h (X).actionObj.action (Y).actionObj.action
    A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines (e).hom) he

omit [IsScalarTower ℚ F A] in
/-- The actual rational Tate map preserves and reflects membership in the carried
frame submodules under the original polarized rational-isogeny frame transport. -/
theorem harrisIntegralFrameLattice_isogeny (X Y : PObj) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (eta : Frame X) (w : Rat X),
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom w ∈
          lattice Y ((frameIso X Y q e he) eta) ↔ w ∈ lattice X eta := by
  let := auxiliaryStarRing D C
  intro e he eta w
  let f := frameIso X Y q e he
  let r := Tate.rationalIso (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.underlyingIso e)
  rw [mem_harrisIntegralFrameLattice, mem_harrisIntegralFrameLattice]
  constructor
  · rintro ⟨v, hv, hev⟩
    refine ⟨v, hv, r.injective ?_⟩
    exact hev
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

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
local notation "levelLattice" =>
  harrisIntegralLevelLattice D C P compatibility h s hs htor hu
local notation "transport" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelIso P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity

omit [IsScalarTower ℚ F A] in
/-- The carried submodule follows the original rational-isogeny transport of
original fixed level orbits. -/
theorem harrisIntegralLevelLattice_isogeny (X Y : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (x : (tower X).obj K) (w : Rat X),
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom w ∈
          levelLattice Y K hK (transport X Y K q e he x) ↔
        w ∈ levelLattice X K hK x := by
  let := auxiliaryStarRing D C
  intro e he x w
  let := rightAction X
  let := rightAction Y
  let f := frameIso X Y q e he
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have hf : ∀ eta (g : G), f (right eta g) = right (f eta) g :=
    Tate.weilAdelicFrameIsogeny_right P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      X.hasDual Y.hasDual X.geometry Y.geometry X.inversePoincare X.evaluation
      Y.inversePoincare Y.evaluation (additivity X Y) X.polarization Y.polarization
      compatibility rationalWeilFunctoriality h X.actionObj.action Y.actionObj.action
      A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
      (RationalAlgebraAction.intertwines e.hom) he
  have htarget : RightOrbit.mk K.toSubgroup (f eta) =
      (transport X Y K q e he x).1 := by
    change RightOrbit.mk K.toSubgroup (f eta) = RightOrbit.map K.toSubgroup f hf x.1
    calc
      _ = RightOrbit.map K.toSubgroup f hf (RightOrbit.mk K.toSubgroup eta) := rfl
      _ = _ := congrArg (RightOrbit.map K.toSubgroup f hf) heta
  rw [harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
      Y K hK _ (f eta) htarget,
    harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
      X K hK x eta heta]
  exact harrisIntegralFrameLattice_isogeny D C P compatibility h s additivity X Y q e he eta w

/-- Restriction of the actual rational Tate isomorphism to the carried submodules
of the original fixed level and its original polarized-isogeny transport. -/
def harrisIntegralLevelLatticeIsogenyEquiv (X Y : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (x : (tower X).obj K),
      letI := integralModule X
      letI := integralModule Y
      levelLattice X K hK x ≃ₗ[Rf]
        levelLattice Y K hK (transport X Y K q e he x) := by
  let := auxiliaryStarRing D C
  intro e he x
  letI := Tate.finiteAdeleModule X.actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  letI := Tate.finiteAdeleModule Y.actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  letI := integralModule X
  letI := integralModule Y
  let r := Tate.rationalIso (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.underlyingIso e)
  have hr := harrisIntegralLevelLattice_isogeny
    D C P compatibility h s additivity hs htor hu X Y K hK q e he x
  refine {
    toFun := fun w => ⟨r w, (hr w).mpr w.property⟩
    invFun := fun w => ⟨r.symm w, (hr (r.symm w)).mp (by
      change r (r.symm (w : Rat Y)) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact w.property)⟩
    left_inv := by
      intro w
      apply Subtype.ext
      exact r.symm_apply_apply w
    right_inv := by
      intro w
      apply Subtype.ext
      exact r.apply_symm_apply w
    map_add' := by
      intro v w
      apply Subtype.ext
      exact r.map_add v w
    map_smul' := by
      intro a w
      apply Subtype.ext
      exact (Tate.finiteAdeleHomMap (Over.mk s) (fun _ => True) h
        (RationalAlgebraAction.underlyingIso e).hom).map_smul
          (a : Global.FiniteAdeles ℚ) w }

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralLevelLatticeIsogenyEquiv_apply (X Y : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (x : (tower X).obj K) (w : levelLattice X K hK x),
      ((harrisIntegralLevelLatticeIsogenyEquiv D C P compatibility h s additivity hs htor hu
        X Y K hK q e he x w :
          levelLattice Y K hK (transport X Y K q e he x)) : Rat Y) =
        Tate.rationalHomMap (Over.mk s) (fun _ => True)
          (RationalAlgebraAction.underlyingIso e).hom w := by
  let := auxiliaryStarRing D C
  intro e he x w
  rfl

omit [IsScalarTower ℚ F A] in
/-- Exact realization of the original carried lattice by the inverse rational
Tate map is equivalent to normalization of the transported original level. -/
theorem harrisIntegralLevelCondition_isogeny_iff (X Y : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (x : (tower X).obj K),
      HarrisIntegralLevelCondition D C P compatibility h s hs htor hu
        Y K (transport X Y K q e he x) ↔
      (∀ w : Rat X, w ∈ levelLattice X K hK x ↔
        ∃ b : GroupScheme.Tate.Full Y.actionObj.abelianScheme.toGrp (Over.mk s),
          Tate.rationalHomMap (Over.mk s) (fun _ => True)
            (RationalAlgebraAction.underlyingIso e).inv
            (GroupScheme.Tate.toRational Y.actionObj.abelianScheme.toGrp
              (Over.mk s) (fun _ => True) b) = w) := by
  let := auxiliaryStarRing D C
  intro e he x
  let r := Tate.rationalIso (Over.mk s) (fun _ => True)
    (RationalAlgebraAction.underlyingIso e)
  have hr := harrisIntegralLevelLattice_isogeny
    D C P compatibility h s additivity hs htor hu X Y K hK q e he x
  rw [harrisIntegralLevelCondition_iff_lattice D C P compatibility h s hs htor hu Y K hK]
  constructor
  · intro hn w
    rw [← hr w]
    change r w ∈ (levelLattice Y K hK (transport X Y K q e he x) : Set (Rat Y)) ↔ _
    rw [hn]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      change r.symm _ = w
      rw [hb, LinearEquiv.symm_apply_apply]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      apply r.symm.injective
      change r.symm _ = r.symm (r w)
      rw [LinearEquiv.symm_apply_apply]
      exact hb
  · intro hn
    apply Set.ext
    intro z
    obtain ⟨w, rfl⟩ := r.surjective z
    change r w ∈ levelLattice Y K hK (transport X Y K q e he x) ↔ _
    refine (hr w).trans ((hn w).trans ?_)
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      apply r.symm.injective
      change r.symm _ = r.symm (r w)
      rw [LinearEquiv.symm_apply_apply]
      exact hb
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      change r.symm _ = w
      rw [hb, LinearEquiv.symm_apply_apply]

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
