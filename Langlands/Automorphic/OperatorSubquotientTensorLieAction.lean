import Langlands.Automorphic.OperatorSubquotientLieAction
import Langlands.Automorphic.OperatorSubquotientTensorHorizontal
import Langlands.Automorphic.TensorLieAction

/-!
# Diagonal Lie actions on actual automorphic operator quotient tensors

The coefficient Lie module is specified explicitly. This internal construction
provides no coefficient group action, relative differential or cohomology.
-/

noncomputable section

universe uF v w

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL TensorProduct

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientTensorLieRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorLieContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorLieSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorLieFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientTensorLieStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientTensorLieRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type v) [AddCommGroup V] [Module ℂ V]
  [LieRingModule (ComplexLieAlgebra F n) V] [LieModule ℂ (ComplexLieAlgebra F n) V]

/-- The Mathlib diagonal action with the quotient's induced differential on the first factor. -/
def tensorComplexLieAction :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Q.Space ⊗[ℂ] V) :=
  LieModule.toEnd ℂ (ComplexLieAlgebra F n) (Q.Space ⊗[ℂ] V)

theorem tensorComplexLieAction_tmul (X : ComplexLieAlgebra F n) (f : Q.Space) (v : V) :
    Q.tensorComplexLieAction V X (f ⊗ₜ[ℂ] v) =
      Q.complexLieAction X f ⊗ₜ[ℂ] v + f ⊗ₜ[ℂ] ⁅X, v⁆ :=
  TensorProduct.LieModule.lie_tmul_right X f v

/-- Restriction to the genuine complement of the real split central directions. -/
def tensorReducedLieAction :
    ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Q.Space ⊗[ℂ] V) :=
  (Q.tensorComplexLieAction V).comp (reducedComplexInclusion F n)

/-- Restriction to the actual complexified compact algebra. -/
def tensorCompactLieAction :
    CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Q.Space ⊗[ℂ] V) :=
  (Q.tensorComplexLieAction V).comp (compactComplexInclusion F n)

theorem tensorReducedLieAction_apply
    (X : ReducedComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorReducedLieAction V X t =
      Q.tensorComplexLieAction V (reducedComplexInclusion F n X) t := rfl

theorem tensorCompactLieAction_apply
    (X : CompactComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorCompactLieAction V X t =
      Q.tensorComplexLieAction V (compactComplexInclusion F n X) t := rfl

/-- The compact restriction through the reduced algebra is the same operator. -/
theorem tensorReducedLieAction_compact (X : CompactComplexLieAlgebra F n) :
    Q.tensorReducedLieAction V (compactToReducedComplex F n X) =
      Q.tensorCompactLieAction V X :=
  congrArg (Q.tensorComplexLieAction V) (reducedComplexInclusion_compact F n X)

/-- Finite adelic translations commute with the entire diagonal complex Lie action. -/
theorem tensorFiniteRepresentation_complexLieAction
    (d : FiniteAdelicGL F n) (X : ComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorFiniteRepresentation V d (Q.tensorComplexLieAction V X t) =
      Q.tensorComplexLieAction V X (Q.tensorFiniteRepresentation V d t) := by
  have h : Q.tensorFiniteRepresentation V d ∘ₗ Q.tensorComplexLieAction V X =
      Q.tensorComplexLieAction V X ∘ₗ Q.tensorFiniteRepresentation V d :=
    TensorProduct.ext' fun f v => by
      simp only [LinearMap.comp_apply, tensorComplexLieAction_tmul, map_add,
        tensorFiniteRepresentation_tmul, Q.finiteRepresentation_complexLieAction]
  exact LinearMap.congr_fun h t

/-- Each finite translation is an actual morphism for the diagonal Lie module. -/
def tensorFiniteLieMap (d : FiniteAdelicGL F n) :
    (Q.Space ⊗[ℂ] V) →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (Q.Space ⊗[ℂ] V) where
  toLinearMap := Q.tensorFiniteRepresentation V d
  map_lie' := Q.tensorFiniteRepresentation_complexLieAction V d _ _

theorem tensorFiniteLieMap_apply (d : FiniteAdelicGL F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorFiniteLieMap V d t = Q.tensorFiniteRepresentation V d t := rfl

theorem tensorFiniteRepresentation_reducedLieAction
    (d : FiniteAdelicGL F n) (X : ReducedComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorFiniteRepresentation V d (Q.tensorReducedLieAction V X t) =
      Q.tensorReducedLieAction V X (Q.tensorFiniteRepresentation V d t) :=
  Q.tensorFiniteRepresentation_complexLieAction V d (reducedComplexInclusion F n X) t

theorem tensorFiniteRepresentation_compactLieAction
    (d : FiniteAdelicGL F n) (X : CompactComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorFiniteRepresentation V d (Q.tensorCompactLieAction V X t) =
      Q.tensorCompactLieAction V X (Q.tensorFiniteRepresentation V d t) :=
  Q.tensorFiniteRepresentation_complexLieAction V d (compactComplexInclusion F n X) t

/-- Explicit coefficient covariance implies covariance of the actual diagonal tensor action. -/
theorem tensorCompactRepresentation_complexLieAction
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (hτ : ∀ (k : standardInfiniteCompact F n) (X : ComplexLieAlgebra F n) (v : V),
      τ k ⁅X, v⁆ = ⁅complexLieConjugation F n k.val X, τ k v⁆)
    (k : standardInfiniteCompact F n) (X : ComplexLieAlgebra F n) (t : Q.Space ⊗[ℂ] V) :
    Q.tensorCompactRepresentation τ k (Q.tensorComplexLieAction V X t) =
      Q.tensorComplexLieAction V (complexLieConjugation F n k.val X)
        (Q.tensorCompactRepresentation τ k t) := by
  have h : Q.tensorCompactRepresentation τ k ∘ₗ Q.tensorComplexLieAction V X =
      Q.tensorComplexLieAction V (complexLieConjugation F n k.val X) ∘ₗ
        Q.tensorCompactRepresentation τ k :=
    TensorProduct.ext' fun f v => by
      simp only [LinearMap.comp_apply, tensorComplexLieAction_tmul, map_add,
        tensorCompactRepresentation_tmul, Q.compactRepresentation_complexLieAction, hτ]
  exact LinearMap.congr_fun h t

/-! ### The canonical projection from the numerator tensor Lie module -/

/-- The quotient Lie projection tensored with the identity of the coefficient Lie module. -/
def tensorComplexLieProjection :
    (Q.upper.Space ⊗[ℂ] V) →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (Q.Space ⊗[ℂ] V) :=
  TensorProduct.LieModule.map Q.complexLieProjection LieModuleHom.id

theorem tensorComplexLieProjection_tmul (f : Q.upper.Space) (v : V) :
    Q.tensorComplexLieProjection V (f ⊗ₜ[ℂ] v) = Q.projection f ⊗ₜ[ℂ] v := rfl

/-- The Lie projection is the right tensor of the canonical module quotient map. -/
theorem tensorComplexLieProjection_toLinearMap :
    (Q.tensorComplexLieProjection V : (Q.upper.Space ⊗[ℂ] V) →ₗ[ℂ] Q.Space ⊗[ℂ] V) =
      LinearMap.rTensor V Q.lower.toSubmodule.mkQ :=
  TensorProduct.ext' fun _ _ => rfl

/-- It has the same underlying map as the compact tensor projection for every coefficient
compact representation. -/
theorem tensorComplexLieProjection_eq_compact
    (τ : Representation ℂ (standardInfiniteCompact F n) V) :
    (Q.tensorComplexLieProjection V : (Q.upper.Space ⊗[ℂ] V) →ₗ[ℂ] Q.Space ⊗[ℂ] V) =
      (Q.tensorCompactProjection τ).toLinearMap :=
  Q.tensorComplexLieProjection_toLinearMap V

/-- The quotient diagonal operator of a projected tensor is the projected numerator operator. -/
theorem tensorComplexLieAction_projection (X : ComplexLieAlgebra F n)
    (t : Q.upper.Space ⊗[ℂ] V) :
    Q.tensorComplexLieAction V X (Q.tensorComplexLieProjection V t) =
      Q.tensorComplexLieProjection V (Q.upper.tensorComplexLieAction V X t) :=
  ((Q.tensorComplexLieProjection V).map_lie X t).symm

theorem tensorComplexLieProjection_finite (d : FiniteAdelicGL F n)
    (t : Q.upper.Space ⊗[ℂ] V) :
    Q.tensorComplexLieProjection V (Q.upper.tensorFiniteRepresentation V d t) =
      Q.tensorFiniteRepresentation V d (Q.tensorComplexLieProjection V t) := by
  have h : (Q.tensorComplexLieProjection V : (Q.upper.Space ⊗[ℂ] V) →ₗ[ℂ] Q.Space ⊗[ℂ] V) ∘ₗ
        Q.upper.tensorFiniteRepresentation V d =
      Q.tensorFiniteRepresentation V d ∘ₗ
        (Q.tensorComplexLieProjection V : (Q.upper.Space ⊗[ℂ] V) →ₗ[ℂ] Q.Space ⊗[ℂ] V) :=
    TensorProduct.ext' fun _ _ => rfl
  exact LinearMap.congr_fun h t

theorem tensorComplexLieProjection_surjective :
    Function.Surjective (Q.tensorComplexLieProjection V) := by
  have h := LinearMap.rTensor_surjective V (Submodule.mkQ_surjective Q.lower.toSubmodule)
  rw [← Q.tensorComplexLieProjection_toLinearMap V] at h
  exact h

/-- A numerator tensor lies in the denominator tensor exactly when its projection vanishes. -/
theorem mem_range_rTensor_lower_iff (t : Q.upper.Space ⊗[ℂ] V) :
    t ∈ LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype) ↔
      Q.tensorComplexLieProjection V t = 0 := by
  have hk : t ∈ LinearMap.ker (LinearMap.rTensor V Q.lower.toSubmodule.mkQ) ↔
      t ∈ LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype) := by
    rw [rTensor_mkQ V Q.lower.toSubmodule]
  have h := LinearMap.congr_fun (Q.tensorComplexLieProjection_toLinearMap V) t
  refine hk.symm.trans (LinearMap.mem_ker.trans ?_)
  exact ⟨fun h0 => h.trans h0, fun h0 => h.symm.trans h0⟩

/-- The actual denominator tensored with the coefficients, as a diagonal Lie submodule. -/
def lowerTensorComplexLieSubmodule :
    LieSubmodule ℂ (ComplexLieAlgebra F n) (Q.upper.Space ⊗[ℂ] V) :=
  { LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype) with
    lie_mem := fun {X} {t} ht => by
      have ht' := (Q.mem_range_rTensor_lower_iff V t).1 ht
      refine (Q.mem_range_rTensor_lower_iff V _).2 ?_
      rw [LieModuleHom.map_lie, ht', lie_zero] }

theorem lowerTensorComplexLieSubmodule_toSubmodule :
    (Q.lowerTensorComplexLieSubmodule V).toSubmodule =
      LinearMap.range (LinearMap.rTensor V Q.lower.toSubmodule.subtype) := rfl

theorem mem_lowerTensorComplexLieSubmodule (t : Q.upper.Space ⊗[ℂ] V) :
    t ∈ Q.lowerTensorComplexLieSubmodule V ↔ Q.tensorComplexLieProjection V t = 0 :=
  Q.mem_range_rTensor_lower_iff V t

/-- Right exactness: the kernel of the Lie projection is exactly the denominator tensor. -/
theorem tensorComplexLieProjection_ker :
    (Q.tensorComplexLieProjection V).ker = Q.lowerTensorComplexLieSubmodule V :=
  LieSubmodule.ext _ _ fun t => by
    rw [LieModuleHom.mem_ker]
    exact (Q.mem_lowerTensorComplexLieSubmodule V t).symm

/-- The quotient tensor Lie module is Mathlib's Lie quotient of the numerator tensor Lie
module by the denominator tensor. -/
def tensorComplexLieQuotientEquiv :
    ((Q.upper.Space ⊗[ℂ] V) ⧸ Q.lowerTensorComplexLieSubmodule V) ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆
      Q.Space ⊗[ℂ] V :=
  { (Submodule.quotEquivOfEq _ _ (Q.lowerTensorComplexLieSubmodule_toSubmodule V)).trans
      (Q.tensorQuotientEquiv V) with
    map_lie' := fun {X} {t} => by
      induction t using Submodule.Quotient.induction_on with
      | H s =>
          exact (Q.tensorComplexLieProjection V).map_lie X s }

theorem tensorComplexLieQuotientEquiv_mk (t : Q.upper.Space ⊗[ℂ] V) :
    Q.tensorComplexLieQuotientEquiv V
        (LieSubmodule.Quotient.mk' (Q.lowerTensorComplexLieSubmodule V) t) =
      Q.tensorComplexLieProjection V t := by
  have h : (Q.tensorComplexLieQuotientEquiv V).toLinearEquiv.toLinearMap ∘ₗ
        (Q.lowerTensorComplexLieSubmodule V).toSubmodule.mkQ =
      (Q.tensorComplexLieProjection V : (Q.upper.Space ⊗[ℂ] V) →ₗ[ℂ] Q.Space ⊗[ℂ] V) :=
    TensorProduct.ext' fun f v => Q.tensorQuotientEquiv_mk f v
  exact LinearMap.congr_fun h t

/-! ### Whole-operator quotient intertwiners and equivalences -/

variable {Q V} {T : OperatorSubquotient F n}
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  [LieRingModule (ComplexLieAlgebra F n) W] [LieModule ℂ (ComplexLieAlgebra F n) W]

/-- Forget a whole-operator quotient intertwiner to the actual complex Lie modules. -/
def complexLieRestrictionMap (L : Q.representation.IntertwiningMap T.representation) :
    Q.Space →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ T.Space where
  toLinearMap := L.toLinearMap
  map_lie' := fun {X} {f} => LinearMap.congr_fun
    (L.isIntertwining' (differentialOperator F n (envelopingGenerator F n X))) f

theorem complexLieRestrictionMap_apply
    (L : Q.representation.IntertwiningMap T.representation) (f : Q.Space) :
    complexLieRestrictionMap L f = L f := rfl

/-- Tensor quotient intertwiners with coefficient Lie module maps. -/
def tensorComplexLieMap (L : Q.representation.IntertwiningMap T.representation)
    (A : V →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) :
    (Q.Space ⊗[ℂ] V) →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (T.Space ⊗[ℂ] W) :=
  TensorProduct.LieModule.map (complexLieRestrictionMap L) A

theorem tensorComplexLieMap_tmul (L : Q.representation.IntertwiningMap T.representation)
    (A : V →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) (f : Q.Space) (v : V) :
    tensorComplexLieMap L A (f ⊗ₜ[ℂ] v) = L f ⊗ₜ[ℂ] A v := rfl

/-- The same tensor Lie map retains finite adelic equivariance. -/
theorem tensorComplexLieMap_finite (L : Q.representation.IntertwiningMap T.representation)
    (A : V →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) (d : FiniteAdelicGL F n) (t : Q.Space ⊗[ℂ] V) :
    tensorComplexLieMap L A (Q.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorComplexLieMap L A t) := by
  have h : (tensorComplexLieMap L A : (Q.Space ⊗[ℂ] V) →ₗ[ℂ] T.Space ⊗[ℂ] W) ∘ₗ
        Q.tensorFiniteRepresentation V d =
      T.tensorFiniteRepresentation W d ∘ₗ
        (tensorComplexLieMap L A : (Q.Space ⊗[ℂ] V) →ₗ[ℂ] T.Space ⊗[ℂ] W) :=
    TensorProduct.ext' fun f v => congrArg (· ⊗ₜ[ℂ] A v)
      (Representation.IntertwiningMap.isIntertwining _ _ L (finiteOperator F n d) f)
  exact LinearMap.congr_fun h t

/-- Tensor quotient and coefficient equivalences without changing the underlying tensor
linear equivalence. -/
def tensorComplexLieEquiv (e : Q.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) :
    (Q.Space ⊗[ℂ] V) ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (T.Space ⊗[ℂ] W) :=
  { TensorProduct.congr e.toLinearEquiv a.toLinearEquiv with
    map_lie' := fun {X t} =>
      (tensorComplexLieMap e.toIntertwiningMap a.toLieModuleHom).map_lie X t }

theorem tensorComplexLieEquiv_tmul (e : Q.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) (f : Q.Space) (v : V) :
    tensorComplexLieEquiv e a (f ⊗ₜ[ℂ] v) = e f ⊗ₜ[ℂ] a v := rfl

/-- The tensor Lie equivalence also preserves the finite adelic action. -/
theorem tensorComplexLieEquiv_finite (e : Q.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ W) (d : FiniteAdelicGL F n) (t : Q.Space ⊗[ℂ] V) :
    tensorComplexLieEquiv e a (Q.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorComplexLieEquiv e a t) :=
  tensorComplexLieMap_finite e.toIntertwiningMap a.toLieModuleHom d t

end OperatorSubquotient
end Langlands.Automorphic
