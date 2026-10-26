import Langlands.Automorphic.TensorHorizontal
import Mathlib.Algebra.Lie.TensorProduct

/-! # Diagonal Lie actions on actual automorphic tensors -/

noncomputable section

universe u v w

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global TensorProduct

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance tensorLieRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorLieContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorLieSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorLieFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorLieStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance tensorLieSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorLieTargetAddCommGroup : AddCommGroup T.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type v) [AddCommGroup V] [Module ℂ V]
  [LieRingModule (ArchimedeanGL.ComplexLieAlgebra F n) V]
  [LieModule ℂ (ArchimedeanGL.ComplexLieAlgebra F n) V]

/-- The Mathlib diagonal action with the actual differential action on the first factor. -/
def tensorComplexLieAction :
    ArchimedeanGL.ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (S.Space ⊗[ℂ] V) :=
  LieModule.toEnd ℂ (ArchimedeanGL.ComplexLieAlgebra F n) (S.Space ⊗[ℂ] V)

@[simp] theorem tensorComplexLieAction_tmul
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (f : S.Space) (v : V) :
    S.tensorComplexLieAction V X (f ⊗ₜ[ℂ] v) =
      S.complexLieAction X f ⊗ₜ[ℂ] v + f ⊗ₜ[ℂ] ⁅X, v⁆ :=
  TensorProduct.LieModule.lie_tmul_right X f v

/-- Restriction to the genuine complement of the real split central directions. -/
def tensorReducedLieAction :
    ArchimedeanGL.ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆
      Module.End ℂ (S.Space ⊗[ℂ] V) :=
  (S.tensorComplexLieAction V).comp (ArchimedeanGL.reducedComplexInclusion F n)

/-- Restriction to the actual complexified compact algebra. -/
def tensorCompactLieAction :
    ArchimedeanGL.CompactComplexLieAlgebra F n →ₗ⁅ℂ⁆
      Module.End ℂ (S.Space ⊗[ℂ] V) :=
  (S.tensorComplexLieAction V).comp (ArchimedeanGL.compactComplexInclusion F n)

@[simp] theorem tensorReducedLieAction_apply
    (X : ArchimedeanGL.ReducedComplexLieAlgebra F n) (t : S.Space ⊗[ℂ] V) :
    S.tensorReducedLieAction V X t =
      S.tensorComplexLieAction V (ArchimedeanGL.reducedComplexInclusion F n X) t := rfl

@[simp] theorem tensorCompactLieAction_apply
    (X : ArchimedeanGL.CompactComplexLieAlgebra F n) (t : S.Space ⊗[ℂ] V) :
    S.tensorCompactLieAction V X t =
      S.tensorComplexLieAction V (ArchimedeanGL.compactComplexInclusion F n X) t := rfl

/-- The compact restriction through the reduced algebra is the same operator. -/
theorem tensorReducedLieAction_compact
    (X : ArchimedeanGL.CompactComplexLieAlgebra F n) :
    S.tensorReducedLieAction V (ArchimedeanGL.compactToReducedComplex F n X) =
      S.tensorCompactLieAction V X := by
  change S.tensorComplexLieAction V
    (ArchimedeanGL.reducedComplexInclusion F n
      (ArchimedeanGL.compactToReducedComplex F n X)) = _
  rw [ArchimedeanGL.reducedComplexInclusion_compact]
  rfl

/-- Finite adelic translations commute with the entire diagonal complex Lie action. -/
theorem tensorFiniteRepresentation_complexLieAction
    (d : FiniteAdelicGL F n) (X : ArchimedeanGL.ComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] V) :
    S.tensorFiniteRepresentation V d (S.tensorComplexLieAction V X t) =
      S.tensorComplexLieAction V X (S.tensorFiniteRepresentation V d t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorComplexLieAction_tmul, map_add, tensorFiniteRepresentation_tmul,
        S.finiteRepresentation_complexLieAction]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Each finite translation is an actual morphism for the diagonal Lie module. -/
def tensorFiniteLieMap (d : FiniteAdelicGL F n) :
    (S.Space ⊗[ℂ] V) →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ (S.Space ⊗[ℂ] V) where
  toLinearMap := S.tensorFiniteRepresentation V d
  map_lie' := S.tensorFiniteRepresentation_complexLieAction V d _ _

@[simp] theorem tensorFiniteLieMap_apply
    (d : FiniteAdelicGL F n) (t : S.Space ⊗[ℂ] V) :
    S.tensorFiniteLieMap V d t = S.tensorFiniteRepresentation V d t := rfl

/-- The finite action commutes with the reduced restriction as well. -/
theorem tensorFiniteRepresentation_reducedLieAction
    (d : FiniteAdelicGL F n) (X : ArchimedeanGL.ReducedComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] V) :
    S.tensorFiniteRepresentation V d (S.tensorReducedLieAction V X t) =
      S.tensorReducedLieAction V X (S.tensorFiniteRepresentation V d t) :=
  S.tensorFiniteRepresentation_complexLieAction V d
    (ArchimedeanGL.reducedComplexInclusion F n X) t

/-- The finite action commutes with the compact restriction as well. -/
theorem tensorFiniteRepresentation_compactLieAction
    (d : FiniteAdelicGL F n) (X : ArchimedeanGL.CompactComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] V) :
    S.tensorFiniteRepresentation V d (S.tensorCompactLieAction V X t) =
      S.tensorCompactLieAction V X (S.tensorFiniteRepresentation V d t) :=
  S.tensorFiniteRepresentation_complexLieAction V d
    (ArchimedeanGL.compactComplexInclusion F n X) t

/-- Explicit coefficient covariance implies covariance of the actual diagonal tensor action. -/
theorem tensorCompactRepresentation_complexLieAction
    (τ : Representation ℂ (standardInfiniteCompact F n) V)
    (hτ : ∀ (k : standardInfiniteCompact F n)
      (X : ArchimedeanGL.ComplexLieAlgebra F n) (v : V),
      τ k ⁅X, v⁆ = ⁅ArchimedeanGL.complexLieConjugation F n k.val X, τ k v⁆)
    (k : standardInfiniteCompact F n) (X : ArchimedeanGL.ComplexLieAlgebra F n)
    (t : S.Space ⊗[ℂ] V) :
    S.tensorCompactRepresentation τ k (S.tensorComplexLieAction V X t) =
      S.tensorComplexLieAction V (ArchimedeanGL.complexLieConjugation F n k.val X)
        (S.tensorCompactRepresentation τ k t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorComplexLieAction_tmul, map_add, tensorCompactRepresentation_tmul,
        S.compactRepresentation_complexLieAction, hτ]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {S T V}
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  [LieRingModule (ArchimedeanGL.ComplexLieAlgebra F n) W]
  [LieModule ℂ (ArchimedeanGL.ComplexLieAlgebra F n) W]

/-- Tensor genuine automorphic intertwiners with coefficient Lie module maps. -/
def tensorComplexLieMap (L : S.Intertwiner T)
    (A : V →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W) :
    (S.Space ⊗[ℂ] V) →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ (T.Space ⊗[ℂ] W) :=
  TensorProduct.LieModule.map L.complexLieRestriction A

@[simp] theorem tensorComplexLieMap_tmul (L : S.Intertwiner T)
    (A : V →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W) (f : S.Space) (v : V) :
    tensorComplexLieMap L A (f ⊗ₜ[ℂ] v) = L f ⊗ₜ[ℂ] A v := rfl

/-- The same tensor Lie map retains finite adelic equivariance. -/
theorem tensorComplexLieMap_finite (L : S.Intertwiner T)
    (A : V →ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W)
    (d : FiniteAdelicGL F n) (t : S.Space ⊗[ℂ] V) :
    tensorComplexLieMap L A (S.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorComplexLieMap L A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      simp only [tensorFiniteRepresentation_tmul, tensorComplexLieMap_tmul, L.finite]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Tensor genuine equivalences without changing the underlying tensor linear equivalence. -/
def tensorComplexLieEquiv (e : S.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W) :
    (S.Space ⊗[ℂ] V) ≃ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ (T.Space ⊗[ℂ] W) :=
  { TensorProduct.congr e.toLinearEquiv a.toLinearEquiv with
    map_lie' := fun {X t} =>
      (tensorComplexLieMap e.toIntertwiningMap a.toLieModuleHom).map_lie X t }

@[simp] theorem tensorComplexLieEquiv_tmul (e : S.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W) (f : S.Space) (v : V) :
    tensorComplexLieEquiv e a (f ⊗ₜ[ℂ] v) = e f ⊗ₜ[ℂ] a v := rfl

/-- The tensor Lie equivalence also preserves the finite adelic action. -/
theorem tensorComplexLieEquiv_finite (e : S.Equivalence T)
    (a : V ≃ₗ⁅ℂ, ArchimedeanGL.ComplexLieAlgebra F n⁆ W)
    (d : FiniteAdelicGL F n) (t : S.Space ⊗[ℂ] V) :
    tensorComplexLieEquiv e a (S.tensorFiniteRepresentation V d t) =
      T.tensorFiniteRepresentation W d (tensorComplexLieEquiv e a t) :=
  tensorComplexLieMap_finite e.toIntertwiningMap a.toLieModuleHom d t

end OperatorRealization
end Langlands.Automorphic
