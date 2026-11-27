import Langlands.AbelianScheme.Tate.WeilPELFrame
import Langlands.AbelianScheme.Tate.WeilFrameMonodromy
import Langlands.AbelianScheme.Tate.WeilGeometricTransportProof
import Langlands.AbelianScheme.Tate.AdelicScalarTopology
import Langlands.AbelianScheme.Tate.RationalTopology
import Langlands.Shimura.PEL.ScalarExtensionTopology
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.CategoryTheory.Galois.ContAction

/-! # Source coordinates, continuity and finite orbits of Weil-frame monodromy -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (σ : Langlands.Shimura.AlgebraInvolution ℚ D)
  (hPEL : RationalPELConditions σ ψ) [Nontrivial V]

local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s
local notation "H" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "rightAction" => weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ s
local notation "coord" => weilAdelicFrameSourceEquiv preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ s σ hPEL

section Coordinates

/-- The source coordinate of `g` is the right translate of the chosen frame by `g`. -/
theorem weilAdelicFrameSourceEquiv_eq_right (eta : Frame) (g : H) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    coord eta g = right eta g := rfl

/-- The identity coordinate is the chosen frame. -/
@[simp] theorem weilAdelicFrameSourceEquiv_one (eta : Frame) : coord eta 1 = eta := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  change right eta (1 : H) = eta
  exact right_one eta

/-- Multiplication of coordinates is successive right translation. -/
theorem weilAdelicFrameSourceEquiv_mul (eta : Frame) (g k : H) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    coord eta (g * k) = right (coord eta g) k := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  change right eta (g * k) = right (right eta g) k
  exact (right_mul eta g k).symm

/-- Two coordinate frames lie in one right orbit of a subgroup `K` exactly when
their coordinates lie in one left coset of `K`. -/
theorem weilAdelicFrameSourceOrbit_eq_iff (eta : Frame) (K : Subgroup H) (g k : H) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    RightOrbit.mk K (coord eta g) = RightOrbit.mk K (coord eta k) ↔ g⁻¹ * k ∈ K := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  rw [RightOrbit.mk_eq_mk]
  constructor
  · rintro ⟨w, hw, hkw⟩
    have hk : k = g * w := (coord eta).injective (by
      rw [weilAdelicFrameSourceEquiv_mul]
      exact hkw)
    simpa only [hk, inv_mul_cancel_left] using hw
  · intro hgk
    refine ⟨g⁻¹ * k, hgk, ?_⟩
    rw [← weilAdelicFrameSourceEquiv_mul, mul_inv_cancel_left]

end Coordinates

section Monodromy

variable (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs
local notation "monodromyAction" => weilAdelicFrameMonodromyAction preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "actionsComm" => weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)

/-- Actual geometric monodromy of a chosen frame, in source coordinates. -/
def weilAdelicFrameCoordinateMonodromy (eta : Frame) : Gamma →* H := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  refine
    { toFun := fun gamma => (coord eta).symm (gamma • eta)
      map_one' := ?_
      map_mul' := ?_ }
  · apply (coord eta).injective
    rw [Equiv.apply_symm_apply, one_smul, weilAdelicFrameSourceEquiv_one]
  · intro gamma delta
    apply (coord eta).injective
    rw [Equiv.apply_symm_apply, mul_smul, weilAdelicFrameSourceEquiv_mul,
      Equiv.apply_symm_apply]
    conv_lhs => rw [← (coord eta).apply_symm_apply (delta • eta)]
    rw [weilAdelicFrameSourceEquiv_eq_right, right_comm]

local notation "rho" => weilAdelicFrameCoordinateMonodromy preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

/-- The defining equation of the coordinate monodromy. -/
theorem weilAdelicFrameCoordinateMonodromy_spec (eta : Frame) (gamma : Gamma) :
    letI : MulAction Gamma Frame := monodromyAction
    coord eta (rho eta gamma) = gamma • eta :=
  (coord eta).apply_symm_apply _

/-- Monodromy is left multiplication in source coordinates. -/
theorem weilAdelicFrameSourceEquiv_monodromy (eta : Frame) (gamma : Gamma) (g : H) :
    letI : MulAction Gamma Frame := monodromyAction
    gamma • coord eta g = coord eta (rho eta gamma * g) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  rw [weilAdelicFrameSourceEquiv_mul, weilAdelicFrameSourceEquiv_eq_right, right_comm,
    weilAdelicFrameCoordinateMonodromy_spec]

/-- A monodromy element fixes the raw orbit of the coordinate `g` exactly when the
conjugate of its coordinate by `g` lies in the subgroup. -/
theorem weilAdelicFrameSourceOrbit_stabilizer_iff
    (eta : Frame) (K : Subgroup H) (gamma : Gamma) (g : H) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    gamma • RightOrbit.mk K (coord eta g) = RightOrbit.mk K (coord eta g) ↔
      g⁻¹ * rho eta gamma * g ∈ K := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  rw [RightOrbit.smul_mk, weilAdelicFrameSourceEquiv_monodromy, eq_comm,
    weilAdelicFrameSourceOrbit_eq_iff, mul_assoc]

/-- The raw orbit of the chosen frame is fixed exactly when all monodromy
coordinates lie in the subgroup. -/
theorem weilAdelicFrameOrbit_base_fixed_iff (eta : Frame) (K : Subgroup H) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K eta ∈ MulAction.fixedPoints Gamma (RightOrbit Frame K) ↔
      ∀ gamma : Gamma, rho eta gamma ∈ K := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  refine forall_congr' (fun gamma => ?_)
  have key := weilAdelicFrameSourceOrbit_stabilizer_iff preservation composition
    unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu eta K gamma 1
  simp only [weilAdelicFrameSourceEquiv_one, inv_one, one_mul, mul_one] at key
  exact key

end Monodromy

section Topology

attribute [local instance] rationalTopology

local notation "R" => Global.FiniteAdeles ℚ
local notation "HP" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "Source" => (Global.FiniteAdeles ℚ) ⊗[ℚ] V
local notation "Target" => RationalFull A (Over.mk s)

omit [Nontrivial V] in
/-- The underlying linear equivalence of a frame is linear over the finite adeles. -/
def weilAdelicFrameScalarLinear (eta : Frame) :
    letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
    Source →ₗ[R] Target := by
  letI := scalarExtensionAlgebraModule D V R
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  refine
    { toFun := eta.1
      map_add' := eta.1.map_add
      map_smul' := ?_ }
  intro r x
  rw [← scalarExtensionAlgebraModule_one_tmul_smul D V R r x, eta.1.map_smul]
  change finiteAdeleAlgebraAction A (Over.mk s) (fun _ => True) h i
    ((1 : D) ⊗ₜ[ℚ] r) (eta.1 x) = _
  rw [finiteAdeleAlgebraAction_tmul, map_one, map_one]
  rfl

omit [Nontrivial V] in
/-- Forward continuity of the underlying map of a frame. -/
theorem continuous_weilAdelicFrame (eta : Frame) :
    letI : TopologicalSpace Source := moduleTopology R Source
    Continuous (fun x : Source => eta.1 x) := by
  let : TopologicalSpace Source := moduleTopology R Source
  let : Module R Target :=
    GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  let : IsTopologicalAddGroup Target := rationalFull_topologicalAddGroup A (Over.mk s)
  let : ContinuousSMul R Target := finiteAdeleModule_continuousSMul A (Over.mk s) h
  exact IsModuleTopology.continuous_of_linearMap
    (weilAdelicFrameScalarLinear preservation composition unitCoherence associativity
      comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
      h i V ψ s eta)

/-- Pointwise evaluation of the frame with a given source coordinate. -/
def weilAdelicFrameEvaluation (eta : Frame) (g : HP) (x : Source) : Target :=
  (coord eta g).1 x

local notation "evaluation" => weilAdelicFrameEvaluation preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ s σ hPEL

theorem weilAdelicFrameEvaluation_injective (eta : Frame) :
    Function.Injective (evaluation eta) := by
  intro g k hgk
  apply (coord eta).injective
  apply Subtype.ext
  apply LinearEquiv.ext
  exact congrFun hgk

theorem continuous_weilAdelicFrameEvaluation (eta : Frame) :
    Continuous (evaluation eta) := by
  let : TopologicalSpace Source := moduleTopology R Source
  apply continuous_pi
  intro x
  change Continuous (fun g : HP => eta.1 (g.val.1 x))
  exact (continuous_weilAdelicFrame preservation composition unitCoherence associativity
    comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
    h i V ψ s eta).comp (ScalarExtensionSimilitudePoints.continuous_apply x)

variable [Module.Finite ℚ V]
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs
local notation "monodromyAction" => weilAdelicFrameMonodromyAction preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "actionsComm" => weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "rho" => weilAdelicFrameCoordinateMonodromy preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

omit [Module.Finite ℚ V] in
/-- If the raw orbit of a frame at a compact open level is fixed, its coordinate
monodromy is continuous: the monodromy then lands in the compact level, on which
the map sending a coordinate to the whole evaluation function of its frame is an
embedding into the product topology. -/
theorem continuous_weilAdelicFrameCoordinateMonodromy_of_fixed
    (eta : Frame) (K : FiniteAdelicScalarExtensionLevel D V ψ) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup) →
    Continuous (fun gamma : Gamma => (show HP from rho eta gamma)) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : T2Space Target := rationalFull_t2Space A (Over.mk s)
  let : CompactSpace K.subgroup := isCompact_iff_compactSpace.mp K.isCompact
  intro heta
  have hrange : ∀ gamma : Gamma, rho eta gamma ∈ K.toSubgroup :=
    (weilAdelicFrameOrbit_base_fixed_iff preservation composition unitCoherence
      associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
      polarizationMap h i V ψ s σ hPEL hs htor hu eta K.toSubgroup).mp heta
  let f : Gamma → K.subgroup := fun gamma => ⟨rho eta gamma, hrange gamma⟩
  let ev : K.subgroup → (Source → Target) := fun k => evaluation eta k.val
  have hev : Topology.IsEmbedding ev :=
    ((continuous_weilAdelicFrameEvaluation preservation composition unitCoherence
      associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
      polarizationMap h i V ψ s σ hPEL eta).comp continuous_subtype_val).isClosedEmbedding
        ((weilAdelicFrameEvaluation_injective preservation composition unitCoherence
          associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
          polarizationMap h i V ψ s σ hPEL eta).comp Subtype.val_injective) |>.isEmbedding
  have hmon : Continuous (ev ∘ f) := by
    apply continuous_pi
    intro x
    have hc := (continuous_rationalFullMonodromy A s hs htor hu).comp
      (continuous_id.prodMk (continuous_const (y := eta.1 x)))
    apply hc.congr
    intro gamma
    have hcoord : coord eta (rho eta gamma) = gamma • eta :=
      weilAdelicFrameCoordinateMonodromy_spec preservation composition unitCoherence
        associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap h i V ψ s σ hPEL hs htor hu eta gamma
    exact (congrArg (fun xi : Frame => xi.1 x) hcoord).symm
  exact continuous_subtype_val.comp (hev.continuous_iff.mpr hmon)

include σ hPEL in
/-- One fixed raw orbit at a compact open level makes the stabilizer of every raw
orbit at every compact open level open. -/
theorem weilAdelicFrameOrbit_stabilizer_isOpen_of_fixed
    (eta : Frame) (K K' : FiniteAdelicScalarExtensionLevel D V ψ) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup) →
    ∀ q : RightOrbit Frame K'.toSubgroup,
      IsOpen (MulAction.stabilizer Gamma q : Set Gamma) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  have hr := continuous_weilAdelicFrameCoordinateMonodromy_of_fixed preservation composition
    unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu eta K heta
  obtain ⟨xi, rfl⟩ := Quotient.exists_rep q
  let g : H := (coord eta).symm xi
  have hc : Continuous (fun gamma : Gamma =>
      (show HP from g)⁻¹ * (show HP from rho eta gamma) * (show HP from g)) :=
    (continuous_const.mul hr).mul continuous_const
  have heq : (MulAction.stabilizer Gamma (RightOrbit.mk K'.toSubgroup xi) : Set Gamma) =
      (fun gamma : Gamma =>
        (show HP from g)⁻¹ * (show HP from rho eta gamma) * (show HP from g)) ⁻¹'
        (K'.subgroup : Set HP) := by
    ext gamma
    change gamma • RightOrbit.mk K'.toSubgroup xi = RightOrbit.mk K'.toSubgroup xi ↔
      g⁻¹ * rho eta gamma * g ∈ K'.toSubgroup
    have key := weilAdelicFrameSourceOrbit_stabilizer_iff preservation composition
      unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu eta K'.toSubgroup gamma g
    simpa only [g, Equiv.apply_symm_apply] using key
  change IsOpen (MulAction.stabilizer Gamma (RightOrbit.mk K'.toSubgroup xi) : Set Gamma)
  rw [heq]
  exact K'.openSubgroup.isOpen.preimage hc

include σ hPEL in
/-- One fixed raw orbit at a compact open level makes every monodromy orbit of raw
orbits at every compact open level finite. -/
theorem weilAdelicFrameOrbit_finite_of_fixed
    (eta : Frame) (K K' : FiniteAdelicScalarExtensionLevel D V ψ) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup) →
    ∀ q : RightOrbit Frame K'.toSubgroup, (MulAction.orbit Gamma q).Finite := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  have hrange : ∀ gamma : Gamma, rho eta gamma ∈ K.toSubgroup :=
    (weilAdelicFrameOrbit_base_fixed_iff preservation composition unitCoherence
      associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
      polarizationMap h i V ψ s σ hPEL hs htor hu eta K.toSubgroup).mp heta
  obtain ⟨xi, rfl⟩ := Quotient.exists_rep q
  let g : HP := (coord eta).symm xi
  let cosetMap : (HP ⧸ K'.subgroup) → RightOrbit Frame K'.toSubgroup :=
    Quotient.lift (fun k : HP => RightOrbit.mk K'.toSubgroup (coord eta k)) (by
      intro k l hkl
      exact (weilAdelicFrameSourceOrbit_eq_iff preservation composition unitCoherence
        associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap h i V ψ s σ hPEL eta K'.toSubgroup k l).mpr
          (QuotientGroup.leftRel_apply.mp hkl))
  apply ((Shimura.CompactOpenLevel.cosetImage_finite K K' g).image cosetMap).subset
  rintro _ ⟨gamma, rfl⟩
  refine ⟨QuotientGroup.mk ((show HP from rho eta gamma) * g),
    ⟨rho eta gamma, hrange gamma, rfl⟩, ?_⟩
  change RightOrbit.mk K'.toSubgroup (coord eta (rho eta gamma * (show H from g))) =
    gamma • RightOrbit.mk K'.toSubgroup xi
  rw [RightOrbit.smul_mk, ← weilAdelicFrameSourceEquiv_monodromy]
  simp only [g, Equiv.apply_symm_apply]

end Topology

end Langlands.AbelianScheme.Tate
