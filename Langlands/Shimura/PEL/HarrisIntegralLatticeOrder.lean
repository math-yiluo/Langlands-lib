import Langlands.Shimura.PEL.HarrisIntegralLevelLattice

/-! # The integral Harris order acting on carried Tate submodules -/

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

open NumberField _root_.Algebra PEL

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C

/-- The actual source tensor-algebra action restricted to the Harris integral order. -/
def harrisIntegralAdeleOrderAction : O →+* Module.End Af Vf :=
  ((scalarExtensionAlgebraAction A A Af).comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] Af)).toRingHom.comp (O).subtype

@[simp] theorem harrisIntegralAdeleOrderAction_tmul (a : O) (r : Af) (x : A) :
    harrisIntegralAdeleOrderAction D C a (r ⊗ₜ[ℚ] x) = r ⊗ₜ[ℚ] ((a : A) * x) := by
  change scalarExtensionAlgebraAction A A Af ((a : A) ⊗ₜ[ℚ] 1) (r ⊗ₜ[ℚ] x) = _
  rw [scalarExtensionAlgebraAction_tmul]
  simp only [one_mul, smul_eq_mul]

/-- The same positive-involution integral order preserves the actual integral source span. -/
theorem harrisIntegralAdeleOrderAction_mem (a : O) {v : Vf} (hv : v ∈ Λf) :
    harrisIntegralAdeleOrderAction D C a v ∈ Λf := by
  let : Module Rf Vf := Module.compHom _ (Rf).subtype
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, rfl⟩ := hv
    rw [harrisIntegralAdeleOrderAction_tmul]
    exact D.harrisHodgePELIntegralAdeleSpan_tmul C
      ⟨(a : A) * (x : A), D.harrisHodgePELIntegralOrder_mul_mem_integralLattice C a.property x.property⟩
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y hx hy hx' hy' =>
    simpa only [map_add] using (Λf).add_mem hx' hy'
  | smul r x hx hx' =>
    change harrisIntegralAdeleOrderAction D C a ((r : Af) • x) ∈ Λf
    rw [map_smul]
    exact (Λf).smul_mem r hx'

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

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "sourceAction" => D.harrisIntegralAdeleOrderAction C

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
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "adelicModule" X:max =>
  letI := auxiliaryStarRing D C
  Tate.finiteAdeleModule (X).actionObj.abelianScheme (Over.mk s) (fun _ => True) h
local notation "integralModule" X:max =>
  letI := adelicModule X
  Module.compHom (Rat X) (Rf).subtype
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] [QuasiSeparatedSpace S] in
/-- The rational action of an integral order element, bundled over the actual integral adeles. -/
def harrisIntegralTateOrderOperator (X : PObj) (a : O) :
    letI := integralModule X
    Module.End Rf (Rat X) := by
  let := auxiliaryStarRing D C
  letI := adelicModule X
  letI := integralModule X
  let f := Tate.finiteAdeleHomMap (Over.mk s) (fun _ => True) h (X.actionObj.action a)
  exact { f.toAddMonoidHom with map_smul' := fun r x => f.map_smul (r : Af) x }

local notation "operator" => harrisIntegralTateOrderOperator D C P h s

omit [IsScalarTower ℚ F A] [QuasiSeparatedSpace S] in
/-- The actual rational Tate operators form a ring action of the unchanged integral order. -/
def harrisIntegralTateOrderAction (X : PObj) :
    letI := integralModule X
    O →+* Module.End Rf (Rat X) := by
  let := auxiliaryStarRing D C
  letI := integralModule X
  refine {
    toFun := operator X
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · ext w
    change Tate.rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
      (X.actionObj.action 1) w = w
    rw [map_one, map_one]
    rfl
  · intro a b
    ext w
    change Tate.rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
      (X.actionObj.action ((a : A) * (b : A))) w = _
    rw [map_mul, map_mul]
    rfl
  · ext w
    change Tate.rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
      (X.actionObj.action 0) w = 0
    rw [map_zero, map_zero]
    rfl
  · intro a b
    ext w
    change Tate.rationalEndAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True)
      (X.actionObj.action ((a : A) + (b : A))) w = _
    rw [map_add, map_add]
    rfl

local notation "tateAction" => harrisIntegralTateOrderAction D C P h s

omit [IsScalarTower ℚ F A] in
/-- Frame linearity intertwines the source order action and actual rational Tate action. -/
theorem harrisIntegralFrame_order (X : PObj) (eta : Frame X) (a : O) (v : Vf) :
    eta.1 (sourceAction a v) = operator X a (eta.1 v) := by
  let := auxiliaryStarRing D C
  have he := eta.1.map_smul (((a : A) ⊗ₜ[ℚ] (1 : Af))) v
  change eta.1 (sourceAction a v) = Tate.rationalEndAction X.actionObj.abelianScheme
    (Over.mk s) (fun _ => True) (X.actionObj.action a)
    (Tate.finiteAdeleAction X.actionObj.abelianScheme (Over.mk s) (fun _ => True) h 1
      (eta.1 v)) at he
  change eta.1 (sourceAction a v) = Tate.rationalHomMap (Over.mk s) (fun _ => True)
    (X.actionObj.action a) (eta.1 v)
  simpa only [map_one, Module.End.one_apply, Tate.rationalEndAction_apply] using he

omit [IsScalarTower ℚ F A] in
/-- The carried frame submodule is preserved by every actual integral Harris order element. -/
theorem harrisIntegralFrameLattice_order_mem (X : PObj) (eta : Frame X) (a : O)
    {w : Rat X} (hw : w ∈ lattice X eta) :
    operator X a w ∈ lattice X eta := by
  obtain ⟨v, hv, rfl⟩ := (mem_harrisIntegralFrameLattice D C P compatibility h s X eta w).mp hw
  rw [← harrisIntegralFrame_order D C P compatibility h s X eta a v,
    harrisIntegralFrameLattice_apply_mem]
  exact D.harrisIntegralAdeleOrderAction_mem C a hv

/-- The integral order acts on the actual frame-image submodule by restriction
of its original rational Tate endomorphisms. -/
def harrisIntegralFrameLatticeOrderAction (X : PObj) (eta : Frame X) :
    letI := integralModule X
    O →+* Module.End Rf (lattice X eta) := by
  letI := integralModule X
  refine {
    toFun := fun a => (tateAction X a).restrict
      (fun w hw => harrisIntegralFrameLattice_order_mem D C P compatibility h s X eta a hw)
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · ext w
    exact LinearMap.congr_fun (map_one (tateAction X)) w
  · intro a b
    ext w
    exact LinearMap.congr_fun (map_mul (tateAction X) a b) w
  · ext w
    exact LinearMap.congr_fun (map_zero (tateAction X)) w
  · intro a b
    ext w
    exact LinearMap.congr_fun (map_add (tateAction X) a b) w

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralFrameLatticeOrderAction_apply (X : PObj)
    (eta : Frame X) (a : O) (w : lattice X eta) :
    letI := auxiliaryStarRing D C
    ((harrisIntegralFrameLatticeOrderAction D C P compatibility h s X eta a w : lattice X eta)
      : Rat X) = Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (X.actionObj.action a) w := rfl

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
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s

omit [IsScalarTower ℚ F A] in
/-- The actual integral order preserves the carried submodule of an original fixed level. -/
theorem harrisIntegralLevelLattice_order_mem (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) (a : O) {w : Rat X}
    (hw : w ∈ levelLattice X K hK x) :
    operator X a w ∈ levelLattice X K hK x := by
  let := rightAction X
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have he := harrisIntegralLevelLattice_eq_frame D C P compatibility h s hs htor hu
    X K hK x eta heta
  rw [he] at hw ⊢
  exact harrisIntegralFrameLattice_order_mem D C P compatibility h s X eta a hw

/-- The original integral Harris order acts on the lattice carried by an original
fixed level orbit, with its actual rational Tate action on the ambient carrier. -/
def harrisIntegralLevelLatticeOrderAction (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) :
    letI := integralModule X
    O →+* Module.End Rf (levelLattice X K hK x) := by
  letI := integralModule X
  refine {
    toFun := fun a => (tateAction X a).restrict
      (fun w hw => harrisIntegralLevelLattice_order_mem
        D C P compatibility h s hs htor hu X K hK x a hw)
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · ext w
    exact LinearMap.congr_fun (map_one (tateAction X)) w
  · intro a b
    ext w
    exact LinearMap.congr_fun (map_mul (tateAction X) a b) w
  · ext w
    exact LinearMap.congr_fun (map_zero (tateAction X)) w
  · intro a b
    ext w
    exact LinearMap.congr_fun (map_add (tateAction X) a b) w

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisIntegralLevelLatticeOrderAction_apply (X : PObj) (K : Level)
    (hK : K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (tower X).obj K) (a : O) (w : levelLattice X K hK x) :
    letI := auxiliaryStarRing D C
    ((harrisIntegralLevelLatticeOrderAction
      D C P compatibility h s hs htor hu X K hK x a w : levelLattice X K hK x) : Rat X) =
      Tate.rationalHomMap (Over.mk s) (fun _ => True) (X.actionObj.action a) w := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
