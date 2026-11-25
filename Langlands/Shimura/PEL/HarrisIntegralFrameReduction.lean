import Langlands.Shimura.PEL.HarrisIntegralSourceCongruence
import Langlands.AbelianScheme.Tate.FullEvaluationKernel
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra

/-! # Torsion reduction of actual normalized Harris frames -/

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
open Langlands.GroupScheme
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
  (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)
local notation "Stab" => (harrisIntegralAdeleStabilizer D C : Subgroup G)
local notation "op" => ScalarExtensionSimilitudePoints.operator
local notation "K" => harrisIntegralAdeleCongruence D C
local notation "multiples" => harrisIntegralSourceMultiples D C
local notation "integralOp" => harrisIntegralSourceOperator D C
local notation "reduceOp" => harrisIntegralSourceReduction D C
local instance : Module Rf Vf := Module.compHom _ (Rf).subtype

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition
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
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation:max "Full" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Full (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "toRat" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True)
local notation:max "rat_injective" X:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.full_toRational_injective (X).actionObj.abelianScheme.toGrp (Over.mk s)
local notation:max "Level" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.Level (X).actionObj.abelianScheme.toGrp (Over.mk s) (m : ℕ)
local notation:max "eval" X:max m:max =>
  letI := auxiliaryStarRing D C
  GroupScheme.Tate.evaluation (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True) m

/-- Restrict the given normalized frame to an additive equivalence with the actual
full integral Tate group, characterized by rationalization into the original frame. -/
def harrisIntegralFrameFull (X : PObj) (eta : Frame X) (hn : Normalized X eta) :
    Λf ≃+ (Full X) := by
  let := auxiliaryStarRing D C
  have hex (v : Λf) := (hn (v : Vf)).mp v.property
  let f : Λf →+ Full X := {
    toFun v := Classical.choose (hex v)
    map_zero' := rat_injective X <| by
      rw [Classical.choose_spec (hex 0), map_zero]
      exact eta.1.map_zero
    map_add' v w := rat_injective X <| by
      rw [Classical.choose_spec (hex (v + w)), map_add, Classical.choose_spec (hex v),
        Classical.choose_spec (hex w)]
      exact eta.1.map_add (v : Vf) (w : Vf) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro v w he
    apply Subtype.ext
    apply eta.1.injective
    exact (Classical.choose_spec (hex v)).symm.trans
      ((congrArg (toRat X) he).trans (Classical.choose_spec (hex w)))
  · intro x
    let v := eta.1.symm (toRat X x)
    have he : toRat X x = eta.1 v := (eta.1.apply_symm_apply _).symm
    have hv : v ∈ Λf := (hn v).mpr ⟨x, he⟩
    refine ⟨⟨v, hv⟩, rat_injective X ?_⟩
    exact (Classical.choose_spec (hex ⟨v, hv⟩)).trans he.symm

local notation:max "full" X:max => harrisIntegralFrameFull D C P compatibility h s X

@[simp] theorem harrisIntegralFrameFull_toRational (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (v : Λf) : toRat X (full X eta hn v) = eta.1 (v : Vf) :=
  Classical.choose_spec ((hn (v : Vf)).mp v.property)

/-- Finite Tate evaluation of the restricted frame on the actual source quotient. -/
def harrisIntegralFrameReduction (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) :
    HarrisIntegralSourceMod D C m.val →+ (Level X m.val) :=
  letI := auxiliaryStarRing D C
  let f : Λf →+ (Level X m.val) := (eval X m).comp (full X eta hn).toAddMonoidHom
  QuotientAddGroup.lift (multiples m.val).toAddSubgroup f (by
    intro v hv
    have hv' : v ∈ multiples m.val := hv
    obtain ⟨w, hw⟩ := hv'
    have he : m.val • w = v := by
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hw
    exact AddMonoidHom.mem_ker.mpr <| calc
      f v = f (m.val • w) := congrArg (fun z : Λf => f z) he.symm
      _ = m.val • f w := map_nsmul f m.val w
      _ = 0 := GroupScheme.Tate.level_nsmul_eq_zero X.actionObj.abelianScheme.toGrp
        (Over.mk s) m.val (f w))

local notation:max "reduction" X:max => harrisIntegralFrameReduction D C P compatibility h s X

@[simp] theorem harrisIntegralFrameReduction_mkQ (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) (v : Λf) :
    reduction X m eta hn ((multiples m.val).mkQ v) = eval X m (full X eta hn v) := rfl

section Geometric

variable (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤))) [IsAlgClosed Ω]

/-- A normalized frame induces an additive equivalence between the actual source
quotient modulo m and the actual m-torsion over the chosen geometric point. -/
def harrisIntegralFrameTorsionEquiv (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) :
    HarrisIntegralSourceMod D C m.val ≃+ (Level X m.val) := by
  let := auxiliaryStarRing D C
  have hinj : Function.Injective (reduction X m eta hn) := by
    intro a b he
    obtain ⟨v, rfl⟩ := (multiples m.val).mkQ_surjective a
    obtain ⟨w, rfl⟩ := (multiples m.val).mkQ_surjective b
    rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ] at he
    have hz : eval X m (full X eta hn (v - w)) = 0 := by
      rw [AddEquiv.map_sub, map_sub, he, sub_self]
    obtain ⟨z, hz⟩ := (GroupScheme.Tate.full_evaluation_eq_zero_iff
      X.actionObj.abelianScheme.toGrp (Over.mk s) m _).mp hz
    obtain ⟨u, rfl⟩ := (full X eta hn).surjective z
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨u, (full X eta hn).injective ?_⟩
    have hns : ∀ (k : ℕ) x, full X eta hn (k • x) = k • full X eta hn x :=
      fun k x => (full X eta hn).toAddMonoidHom.map_nsmul k x
    rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, hns, hz]
  have hsur : Function.Surjective (reduction X m eta hn) := by
    intro t
    obtain ⟨z, hz⟩ := Tate.full_evaluation_surjective_at hu X.actionObj.abelianScheme s m t
    obtain ⟨v, rfl⟩ := (full X eta hn).surjective z
    exact ⟨(multiples m.val).mkQ v, hz⟩
  exact AddEquiv.ofBijective (reduction X m eta hn) ⟨hinj, hsur⟩

local notation:max "torsionEquiv" X:max => harrisIntegralFrameTorsionEquiv D C P compatibility h s hu X

@[simp] theorem harrisIntegralFrameTorsionEquiv_mkQ (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) (v : Λf) :
    torsionEquiv X m eta hn ((multiples m.val).mkQ v) = eval X m (full X eta hn v) := rfl

end Geometric

/-- Precomposing a normalized frame with an integral source operator precomposes
its torsion reduction by the actual quotient operator. -/
theorem harrisIntegralFrameReduction_right (X : PObj) (m : Index (fun _ => True))
    (eta : Frame X) (hn : Normalized X eta) (g : Stab) :
    letI := auxiliaryStarRing D C
    letI := rightAction X
    ∀ (hn' : Normalized X (right eta g.val)) (x : HarrisIntegralSourceMod D C m.val),
      reduction X m (right eta g.val) hn' x = reduction X m eta hn (reduceOp m.val g x) := by
  let := auxiliaryStarRing D C
  let := rightAction X
  intro hn' x
  obtain ⟨v, rfl⟩ := (multiples m.val).mkQ_surjective x
  change reduction X m (right eta g.val) hn' ((multiples m.val).mkQ v) =
    reduction X m eta hn ((multiples m.val).mkQ (integralOp g v))
  rw [harrisIntegralFrameReduction_mkQ, harrisIntegralFrameReduction_mkQ]
  rfl

variable (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤))) [IsAlgClosed Ω]

include hu in
/-- Among normalized frames of one fixed datum at one geometric point, equality
of the reductions detects precisely the original right principal-congruence orbit. -/
theorem harrisIntegralFrameReduction_eq_iff_rightOrbit (X : PObj)
    (m : Index (fun _ => True))
    (eta xi : Frame X) (hn : Normalized X eta) (hx : Normalized X xi) :
    letI := auxiliaryStarRing D C
    letI : MulAction Gᵐᵒᵖ (Frame X) := rightAction X
    reduction X m eta hn = reduction X m xi hx ↔
      RightOrbit.mk (K m.val) eta = RightOrbit.mk (K m.val) xi := by
  let := auxiliaryStarRing D C
  let _ : MulAction Gᵐᵒᵖ (Frame X) := rightAction X
  have hright (g : Stab) (hn' : Normalized X (right eta g.val)) :=
    harrisIntegralFrameReduction_right D C P compatibility h s X m eta hn g hn'
  have hinj : Function.Injective (reduction X m eta hn) :=
    (harrisIntegralFrameTorsionEquiv D C P compatibility h s hu X m eta hn).injective
  constructor
  · intro heq
    have hex : ∃ g : G, right eta g = xi := by
      let _ := scalarExtensionAlgebraModule A A Af
      let _ := Tate.finiteAdeleAlgebraModule X.actionObj.abelianScheme (Over.mk s)
        (fun _ => True) h X.actionObj.action
      let _ := GroupScheme.Tate.finiteAdeleModule X.actionObj.abelianScheme.toGrp (Over.mk s)
        (fun _ => True) h
      let _ := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
        (fun _ => True) h
      exact FormIso.exists_precomp_eq eta xi
    obtain ⟨g, hg⟩ := hex
    subst xi
    have hg' : g ∈ Stab := fun v => (hn (op g v)).trans (hx v).symm
    apply (RightOrbit.mk_eq_mk (K m.val) eta (right eta g)).mpr
    refine ⟨g, Subgroup.mem_map.mpr ⟨⟨g, hg'⟩, ?_, rfl⟩, rfl⟩
    change reduceOp m.val ⟨g, hg'⟩ = 1
    apply LinearMap.ext
    intro x
    apply hinj
    exact (hright ⟨g, hg'⟩ hx x).symm.trans (DFunLike.congr_fun heq x).symm
  · intro heq
    obtain ⟨g, hg, rfl⟩ := (RightOrbit.mk_eq_mk (K m.val) eta xi).mp heq
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    change reduceOp m.val g' = 1 at hg'
    apply AddMonoidHom.ext
    intro x
    exact (congrArg (fun z => reduction X m eta hn z) (DFunLike.congr_fun hg' x)).symm.trans
      (hright g' hx x).symm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
