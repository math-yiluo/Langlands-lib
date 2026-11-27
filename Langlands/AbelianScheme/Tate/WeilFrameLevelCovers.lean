import Langlands.AbelianScheme.Tate.WeilFrameLevelMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricContinuousActionEquivalenceProof
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

/-! # Finite étale covers of Weil-frame monodromy orbits -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- If a morphism `f : T ⟶ S` factors through a cover `Y` by `g`, and a geometric point
`t` of `T` is carried by `g` to the lift `y`, then the image of `π₁(T, t)` fixes `y`. -/
theorem fundamentalGroupMap_smul_eq_of_factor {S T : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : T ⟶ S) (t : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S) (hts : t ≫ f = s)
    (ht : ∀ Y : Cover T, Finite (Fiber t Y)) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    {Y : Cover S} (y : Fiber s Y) (g : T ⟶ Y.obj.left) (hg : g ≫ Y.obj.hom = f)
    (hy : t ≫ g = y.left) (σ : FundamentalGroup t ht) :
    fundamentalGroupMap f t s hts ht hs σ • y = y := by
  let Z : Cover T := cover (𝟙 T)
  let z : Fiber t Z := Over.homMk t (by simp [Z, cover])
  have hz : ∀ z' : Fiber t Z, z' = z := by
    intro z'
    apply Over.OverMorphism.ext
    have h1 : z'.left ≫ (𝟙 T) = t := Over.w z'
    show z'.left = t
    exact (Category.comp_id z'.left).symm.trans h1
  apply Over.OverMorphism.ext
  rw [fundamentalGroupMap_smul_left_of_comp f t s hts ht hs σ y z g
    (by simpa [Z, cover] using hg) (by simpa [z] using hy)]
  rw [hz (σ • z)]
  simpa [z] using hy

end Langlands.AlgebraicGeometry.FiniteEtale

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
  (V : Type u) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (σ : Langlands.Shimura.AlgebraInvolution ℚ D)
  (hPEL : RationalPELConditions σ ψ) [Nontrivial V] [Module.Finite ℚ V]
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s
local notation "H" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "rightAction" => weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility polarizationMap h i V ψ s
local notation "Gamma" => FundamentalGroup s hs
local notation "monodromyAction" => weilAdelicFrameMonodromyAction preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "actionsComm" => weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i V ψ s hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Level" => FiniteAdelicScalarExtensionLevel D V ψ

open scoped FintypeCatDiscrete

include σ hPEL in
/-- The monodromy orbit of a raw frame orbit, with its finite continuous action,
whenever the raw orbit of some frame at a compact open level is fixed. -/
def weilAdelicFrameOrbitAction (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup) →
    RightOrbit Frame K'.toSubgroup → ContAction FintypeCat.{u} Gamma := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  letI : Fintype (MulAction.orbit Gamma q) :=
    (weilAdelicFrameOrbit_finite_of_fixed preservation composition unitCoherence
      associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
      polarizationMap h i V ψ s σ hPEL hs htor hu eta K K' heta q).fintype
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
  exact weilAdelicFrameOrbit_stabilizer_isOpen_of_fixed preservation composition
    unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu eta K K' heta r.val

local notation "orbitAction" => weilAdelicFrameOrbitAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

variable [ConnectedSpace S] [IsLocallyNoetherian S] [IsAlgClosed Ω]

/-- A finite étale cover whose geometric fibre is the monodromy orbit of a raw orbit. -/
def weilAdelicFrameOrbitCover (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    RightOrbit.mk K.toSubgroup eta ∈
      MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup) →
    RightOrbit Frame K'.toSubgroup → Cover S := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro heta q
  exact (continuousActionFunctor s hs).objPreimage (orbitAction eta K K' heta q)

local notation "orbitCover" => weilAdelicFrameOrbitCover preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

/-- The fibre action of the cover is the orbit action. -/
def weilAdelicFrameOrbitCoverActionIso (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup),
      (continuousActionFunctor s hs).obj (orbitCover eta K K' heta q) ≅
        orbitAction eta K K' heta q := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro heta q
  exact (continuousActionFunctor s hs).objObjPreimageIso (orbitAction eta K K' heta q)

local notation "orbitCoverActionIso" => weilAdelicFrameOrbitCoverActionIso preservation
  composition unitCoherence associativity comparison symmetry stability compatibility hA
  geometryA MA evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

/-- The geometric lifts into the cover are exactly the monodromy orbit. -/
def weilAdelicFrameOrbitCoverFiberEquiv (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup),
      Fiber s (orbitCover eta K K' heta q) ≃ MulAction.orbit Gamma q := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  exact FintypeCat.equivEquivIso.symm
    ((forget₂ (ContAction FintypeCat Gamma) FintypeCat).mapIso
      (orbitCoverActionIso eta K K' heta q))

local notation "orbitCoverFiberEquiv" => weilAdelicFrameOrbitCoverFiberEquiv preservation
  composition unitCoherence associativity comparison symmetry stability compatibility hA
  geometryA MA evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

/-- The fibre comparison intertwines the fibre action and the orbit action. -/
theorem weilAdelicFrameOrbitCoverFiberEquiv_smul (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup) (gamma : Gamma)
      (x : Fiber s (orbitCover eta K K' heta q)),
      orbitCoverFiberEquiv eta K K' heta q (gamma • x) =
        gamma • orbitCoverFiberEquiv eta K K' heta q x := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q gamma x
  exact ConcreteCategory.congr_hom
    ((orbitCoverActionIso eta K K' heta q).hom.hom.comm gamma) x

/-- The lift corresponding to the raw orbit itself. -/
def weilAdelicFrameOrbitCoverPoint (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup), Fiber s (orbitCover eta K K' heta q) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  exact (orbitCoverFiberEquiv eta K K' heta q).symm ⟨q, MulAction.mem_orbit_self q⟩

local notation "orbitCoverPoint" => weilAdelicFrameOrbitCoverPoint preservation
  composition unitCoherence associativity comparison symmetry stability compatibility hA
  geometryA MA evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu

theorem weilAdelicFrameOrbitCoverFiberEquiv_point (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup),
      (orbitCoverFiberEquiv eta K K' heta q (orbitCoverPoint eta K K' heta q)).val = q := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q
  simp only [weilAdelicFrameOrbitCoverPoint, Equiv.apply_symm_apply]

/-- Every monodromy element fixing the distinguished lift fixes the raw orbit. -/
theorem weilAdelicFrameOrbitCoverPoint_smul_eq (eta : Frame) (K K' : Level) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (heta : RightOrbit.mk K.toSubgroup eta ∈
        MulAction.fixedPoints Gamma (RightOrbit Frame K.toSubgroup))
      (q : RightOrbit Frame K'.toSubgroup) (gamma : Gamma),
      gamma • orbitCoverPoint eta K K' heta q = orbitCoverPoint eta K K' heta q →
        gamma • q = q := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro heta q gamma hfix
  have hp : orbitCoverFiberEquiv eta K K' heta q (orbitCoverPoint eta K K' heta q) =
      ⟨q, MulAction.mem_orbit_self q⟩ :=
    Subtype.ext (weilAdelicFrameOrbitCoverFiberEquiv_point preservation composition
      unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
      evaluationA polarizationMap h i V ψ s σ hPEL hs htor hu eta K K' heta q)
  have hval := congrArg (fun x => (orbitCoverFiberEquiv eta K K' heta q x).val) hfix
  simp only at hval
  rw [weilAdelicFrameOrbitCoverFiberEquiv_smul, hp] at hval
  exact hval

end Langlands.AbelianScheme.Tate
