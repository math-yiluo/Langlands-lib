import Langlands.Global.AdelicBlockProjectedSpecialization
import Langlands.Automorphic.OperatorCompactSpecialization
import Langlands.Representation.KFiniteDual

/-! # Compact lifts in the smooth adelic block model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped MonoidAlgebra

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GroupScheme
open Langlands.GeneralLinear (BlockShape)
open EisensteinJet AdelicBlockEisensteinGeometry
open Langlands.GroupScheme.GeneralLinear (blockParabolicScheme blockShapeWeight)

variable (F : Type u) [Field F] [NumberField F] (r : ℕ) (B : BlockShape (r + 1))
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "n" => r + 1
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S
local notation "R" => smoothCompactFiniteAction F B S
local notation "C" => smoothCompactAction F B S
local notation "K" => standardInfiniteCompact F n
local notation "Ops" => FreeOperatorAlgebra F n
local notation "Stable" => StableAutomorphicFunctions F n
local notation "op" => blockSectionOperatorAction F r B S
local notation "finOp" => fun g : FiniteAdelicGL F n => FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))
local notation "cmpOp" => fun k : K => FreeAlgebra.ι ℂ (Sum.inl (Sum.inr k))

local instance blockCompactSpecializationVGroup : AddCommGroup V := Submodule.addCommGroup _
local instance blockCompactSpecializationWGroup : AddCommGroup W := Submodule.addCommGroup _
local instance blockCompactSpecializationRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance blockCompactSpecializationContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance blockCompactSpecializationSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance blockCompactSpecializationStableGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance blockCompactSpecializationStableModule : Module ℂ Stable := Submodule.module _
local instance blockCompactSpecializationParabolicAffine :
    IsAffine (blockParabolicScheme (Fin n) (CommRingCat.of F) (blockShapeWeight B)).X.left :=
  blockParabolic_isAffine F B
local instance blockCompactSpecializationTorusMono :
    Mono (blockRootData F B).root.data.i.hom.hom.left := (blockRootData F B).torus_mono
local instance blockCompactSpecializationFactorMono :
    Mono (CommGroupScheme.groupHom (blockRootData F B).root.data.f).hom.hom.left :=
  (blockRootData F B).factor_mono
local instance blockCompactSpecializationWeylFinite :
    Fintype (Langlands.GroupScheme.relativeWeylGroup (blockRootData F B).root.data.i) :=
  @Fintype.ofFinite _ (blockRootData F B).finite_weylGroup

private theorem originalFinite_isSmooth : Langlands.IsSmooth R := by
  intro w
  obtain ⟨L, hL⟩ := w.val.property
  exact ⟨L, fun l => Subtype.ext (Subtype.ext (hL l))⟩

private theorem originalCompact_isFiniteVector (w : W) : FiniteVectors.IsFiniteVector C w := by
  let i : Representation.IntertwiningMap C (finiteSmoothCompactAction F B S) :=
    { toLinearMap := (W).subtype
      isIntertwining' _ := rfl }
  exact (FiniteVectors.isFiniteVector_map_iff i Subtype.val_injective w).mp
    ((mem_smoothCompactFiniteSections F B S w.val).mp w.property).1

/-- The compact action on the smooth block sections is algebraically semisimple. -/
theorem smoothCompactAction_isSemisimple : IsSemisimpleModule ℂ[K] (C).asModule := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardInfiniteCompact F n)
  apply Langlands.KFiniteDual.isSemisimpleModule (originalCompact_isFiniteVector F r B S)
  intro w l
  let O := FiniteVectors.orbitSpan C w
  let : FiniteDimensional ℂ O := originalCompact_isFiniteVector F r B S w
  let j : O →ₗ[ℂ] (AdelicGL F n → ℂ) :=
    { toFun := fun f => f.val.val.val.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hj : Function.Injective j := fun a b h =>
    Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext h)))
  obtain ⟨x, e, he⟩ := exists_evaluationEquiv j hj
  let orbit (k : K) : O := ⟨C k w, FiniteVectors.action_mem_orbitSpan C k w⟩
  have hc : Continuous fun k : K => e (orbit k) := by
    apply continuous_pi
    intro i
    simp only [he]
    change Continuous fun k : K => w.val.val.val (x i * AdelicGL.ofInfinite F n k.val)
    exact (continuous_smoothBlockSection F B S w).comp
      (continuous_const.mul ((AdelicGL.ofInfinite F n).continuous.comp continuous_subtype_val))
  have hl := (l.comp (O.subtype.comp e.symm.toLinearMap)).continuous_of_finiteDimensional
  have heval : (fun k : K => l (C k w)) =
      (l.comp (O.subtype.comp e.symm.toLinearMap)) ∘ fun k : K => e (orbit k) := by
    funext k
    change l (C k w) = l (O.subtype (e.symm (e (orbit k))))
    rw [e.symm_apply_apply]
    rfl
  rw [heval]
  exact hl.comp hc

/-- A convergence-region injectivity input tested on every finite-dimensional
range of an endomorphism of the actual block sections. -/
def BlockEisensteinInjectiveOnFiniteRanges : Prop :=
  ∀ π : Module.End ℂ W, FiniteDimensional ℂ π.range → BlockEisensteinInjectiveOnAnchor F r B S π

/-- A simple quotient of an invariant numerator in the original block action
has a compact-projected automorphic realization under the two analytic inputs. -/
theorem exists_freeOperatorQuotient_of_block_subquotient
    (hS : ∀ i, (S i).IsJointlyAdmissible)
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : BlockEisensteinInjectiveOnFiniteRanges F r B S)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (aY : Ops →ₐ[ℂ] Module.End ℂ Y) (ha : Representation.IsIrreducible aY.toMonoidHom)
    (σ : Representation ℂ (FiniteAdelicGL F n) Y) (ν : Representation ℂ K Y)
    (hσ : ∀ g, aY (finOp g) = σ g) (hν : ∀ k, aY (cmpOp k) = ν k)
    (U : Subrepresentation (op 0).toMonoidHom)
    (q : U.toRepresentation.IntertwiningMap aY.toMonoidHom) (hq : Function.Surjective q) :
    letI := moduleOfAlgebraAction aY
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F n)
    ∃ U' : Submodule Ops Stable, ∃ q' : U' →ₗ[Ops] Y, Function.Surjective q' := by
  let := smoothCompactAction_isSemisimple F r B S
  let L := FiniteAdelicGL.standardIntegral F n
  have hcomm (g : FiniteAdelicGL F n) (k : K) (w : W) : R g (C k w) = C k (R g w) :=
    Subtype.ext (Subtype.ext (RealizedSections.finiteAction_infiniteCompactAction F B S g k w.val.val))
  obtain ⟨π, hπ, hProjection, y, hy, hFiber⟩ := exists_jointCompactProjection_of_operatorSpecialization
    op 0 R C σ ν finOp cmpOp
    (blockSectionOperatorAction_finite_at_zero F r B S) (blockSectionOperatorAction_compact F r B S)
    hσ hν (originalFinite_isSmooth F r B S) (originalCompact_isFiniteVector F r B S)
    hcomm (smoothCompactFiniteSections_isJointlyAdmissible F B S hS) L
    (FiniteAdelicGL.isCompact_standardIntegral F n)
    (fun t g => blockSectionOperatorAction_finiteIntegral F r B S t g.val g.property) ha U q hq
  let := hπ
  exact exists_freeOperatorQuotient_of_block_projected_specialization F r B S hS π hcont
    (hinj π hπ) hProjection aY ha _ (operatorNumeratorQuotient U q) hq y hy hFiber

end Langlands.Global.AdelicBlockScalarSections
