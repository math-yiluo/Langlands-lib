import Langlands.Global.ArchimedeanLieAlgebra
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.RingTheory.Flat.Basic

/-! # The concrete compact matrix Lie algebra and Cartan decomposition -/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator
open NumberField

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

instance : Star (RealLieAlgebra K n) :=
  inferInstanceAs (Star (ArchimedeanMatrix K n))

instance : StarAddMonoid (RealLieAlgebra K n) :=
  inferInstanceAs (StarAddMonoid (ArchimedeanMatrix K n))

instance : StarModule ℝ (RealLieAlgebra K n) :=
  inferInstanceAs (StarModule ℝ (ArchimedeanMatrix K n))

local instance : Ring (RealLieAlgebra K n) :=
  inferInstanceAs (Ring (ArchimedeanMatrix K n))

local instance : StarRing (RealLieAlgebra K n) :=
  inferInstanceAs (StarRing (ArchimedeanMatrix K n))

/-- The matrix Cartan involution: negative transpose at real places and
negative conjugate transpose at complex places. -/
def cartanInvolution : RealLieAlgebra K n ≃ₗ⁅ℝ⁆ RealLieAlgebra K n where
  toFun X := -star X
  invFun X := -star X
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by simp [add_comm]
  map_smul' r X := by simp
  map_lie' := by
    intro X Y
    change -star (X * Y - Y * X) = (-star X) * (-star Y) - (-star Y) * (-star X)
    simp [star_sub, star_mul]

@[simp]
theorem cartanInvolution_apply (X : RealLieAlgebra K n) :
    cartanInvolution K n X = -star X := rfl

@[simp]
theorem cartanInvolution_involutive (X : RealLieAlgebra K n) :
    cartanInvolution K n (cartanInvolution K n X) = X := by simp

@[simp]
theorem cartanInvolution_real (X : RealLieAlgebra K n) (i j : Fin n)
    (v : {v : InfinitePlace K // v.IsReal}) :
    (realLieAlgebraToMatrix K n (cartanInvolution K n X) i j).1 v =
      -(realLieAlgebraToMatrix K n X j i).1 v := rfl

@[simp]
theorem cartanInvolution_complex (X : RealLieAlgebra K n) (i j : Fin n)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    (realLieAlgebraToMatrix K n (cartanInvolution K n X) i j).2 v =
      -star ((realLieAlgebraToMatrix K n X j i).2 v) := rfl

/-- The actual skew-adjoint matrix Lie subalgebra over the reals. -/
def compactLieSubalgebra : LieSubalgebra ℝ (RealLieAlgebra K n) :=
  { skewAdjoint.submodule ℝ (RealLieAlgebra K n) with
    lie_mem' := by
      intro X Y hX hY
      change star X = -X at hX
      change star Y = -Y at hY
      change star (X * Y - Y * X) = -(X * Y - Y * X)
      simp [star_sub, star_mul, hX, hY] }

/-- The complementary self-adjoint real submodule. -/
def cartanComplement : Submodule ℝ (RealLieAlgebra K n) :=
  selfAdjoint.submodule ℝ (RealLieAlgebra K n)

@[simp]
theorem mem_compactLieSubalgebra (X : RealLieAlgebra K n) :
    X ∈ compactLieSubalgebra K n ↔ star X = -X := Iff.rfl

@[simp]
theorem mem_cartanComplement (X : RealLieAlgebra K n) :
    X ∈ cartanComplement K n ↔ star X = X := Iff.rfl

theorem mem_compactLieSubalgebra_iff_fixed (X : RealLieAlgebra K n) :
    X ∈ compactLieSubalgebra K n ↔ cartanInvolution K n X = X := by
  simp only [mem_compactLieSubalgebra, cartanInvolution_apply, neg_eq_iff_eq_neg]

theorem mem_cartanComplement_iff_neg (X : RealLieAlgebra K n) :
    X ∈ cartanComplement K n ↔ cartanInvolution K n X = -X := by
  simp

/-- Compact membership is precisely skew symmetry at real places and skew
Hermitian symmetry at complex places. -/
theorem mem_compactLieSubalgebra_iff_coordinates (X : RealLieAlgebra K n) :
    X ∈ compactLieSubalgebra K n ↔
      (∀ (v : {v : InfinitePlace K // v.IsReal}) (i j : Fin n),
        (realLieAlgebraToMatrix K n X j i).1 v =
          -(realLieAlgebraToMatrix K n X i j).1 v) ∧
      (∀ (v : {v : InfinitePlace K // v.IsComplex}) (i j : Fin n),
        star ((realLieAlgebraToMatrix K n X j i).2 v) =
          -(realLieAlgebraToMatrix K n X i j).2 v) := by
  rw [mem_compactLieSubalgebra]
  constructor
  · intro h
    exact ⟨fun v i j => congrArg (fun A => (realLieAlgebraToMatrix K n A i j).1 v) h,
      fun v i j => congrArg (fun A => (realLieAlgebraToMatrix K n A i j).2 v) h⟩
  · intro h
    apply (realLieAlgebraToMatrix K n).injective
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      exact h.1 v i j
    · funext v
      exact h.2 v i j

/-- Complementary membership is precisely symmetry at real places and
Hermitian symmetry at complex places. -/
theorem mem_cartanComplement_iff_coordinates (X : RealLieAlgebra K n) :
    X ∈ cartanComplement K n ↔
      (∀ (v : {v : InfinitePlace K // v.IsReal}) (i j : Fin n),
        (realLieAlgebraToMatrix K n X j i).1 v =
          (realLieAlgebraToMatrix K n X i j).1 v) ∧
      (∀ (v : {v : InfinitePlace K // v.IsComplex}) (i j : Fin n),
        star ((realLieAlgebraToMatrix K n X j i).2 v) =
          (realLieAlgebraToMatrix K n X i j).2 v) := by
  rw [mem_cartanComplement]
  constructor
  · intro h
    exact ⟨fun v i j => congrArg (fun A => (realLieAlgebraToMatrix K n A i j).1 v) h,
      fun v i j => congrArg (fun A => (realLieAlgebraToMatrix K n A i j).2 v) h⟩
  · intro h
    apply (realLieAlgebraToMatrix K n).injective
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      exact h.1 v i j
    · funext v
      exact h.2 v i j

theorem compactLieSubalgebra_lie {X Y : RealLieAlgebra K n}
    (hX : X ∈ compactLieSubalgebra K n) (hY : Y ∈ compactLieSubalgebra K n) :
    ⁅X, Y⁆ ∈ compactLieSubalgebra K n :=
  (compactLieSubalgebra K n).lie_mem hX hY

theorem compactLieSubalgebra_lie_cartanComplement {X Y : RealLieAlgebra K n}
    (hX : X ∈ compactLieSubalgebra K n) (hY : Y ∈ cartanComplement K n) :
    ⁅X, Y⁆ ∈ cartanComplement K n := by
  rw [mem_compactLieSubalgebra] at hX
  rw [mem_cartanComplement] at hY ⊢
  change star (X * Y - Y * X) = X * Y - Y * X
  simp [star_mul, hX, hY, sub_eq_add_neg, add_comm]

theorem cartanComplement_lie {X Y : RealLieAlgebra K n}
    (hX : X ∈ cartanComplement K n) (hY : Y ∈ cartanComplement K n) :
    ⁅X, Y⁆ ∈ compactLieSubalgebra K n := by
  rw [mem_cartanComplement] at hX hY
  rw [mem_compactLieSubalgebra]
  change star (X * Y - Y * X) = -(X * Y - Y * X)
  simp [star_sub, star_mul, hX, hY]

/-- Projection to the compact part, `(X - X*) / 2`. -/
def compactProjection : RealLieAlgebra K n →ₗ[ℝ] compactLieSubalgebra K n :=
  skewAdjointPart ℝ

/-- Projection to the complementary part, `(X + X*) / 2`. -/
def cartanComplementProjection : RealLieAlgebra K n →ₗ[ℝ] cartanComplement K n :=
  selfAdjointPart ℝ

@[simp]
theorem compactProjection_apply (X : RealLieAlgebra K n) :
    (compactProjection K n X : RealLieAlgebra K n) = (2 : ℝ)⁻¹ • (X - star X) := rfl

@[simp]
theorem cartanComplementProjection_apply (X : RealLieAlgebra K n) :
    (cartanComplementProjection K n X : RealLieAlgebra K n) =
      (2 : ℝ)⁻¹ • (X + star X) := rfl

/-- The direct-sum decomposition into compact and complementary matrix directions. -/
def cartanDecomposition : RealLieAlgebra K n ≃ₗ[ℝ]
    (compactLieSubalgebra K n) × (cartanComplement K n) :=
  (StarModule.decomposeProdAdjoint ℝ (RealLieAlgebra K n)).trans
    (LinearEquiv.prodComm ℝ _ _)

@[simp]
theorem cartanDecomposition_apply (X : RealLieAlgebra K n) :
    cartanDecomposition K n X = (compactProjection K n X, cartanComplementProjection K n X) := rfl

@[simp]
theorem cartanDecomposition_symm_apply
    (X : compactLieSubalgebra K n) (Y : cartanComplement K n) :
    (cartanDecomposition K n).symm (X, Y) = (X : RealLieAlgebra K n) + Y := by
  change (Y : RealLieAlgebra K n) + X = X + Y
  exact add_comm _ _

theorem compactProjection_add_cartanComplementProjection (X : RealLieAlgebra K n) :
    (compactProjection K n X : RealLieAlgebra K n) + cartanComplementProjection K n X = X := by
  exact (cartanDecomposition_symm_apply K n _ _).symm.trans
    ((cartanDecomposition K n).symm_apply_apply X)

/-- The scalar extension of the compact real Lie algebra. -/
abbrev CompactComplexLieAlgebra := ℂ ⊗[ℝ] (compactLieSubalgebra K n)

/-- The complex-linear Lie map induced by the actual compact inclusion. -/
def compactComplexInclusion : CompactComplexLieAlgebra K n →ₗ⁅ℂ⁆ ComplexLieAlgebra K n :=
  { (compactLieSubalgebra K n).toSubmodule.subtype.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (compactLieSubalgebra K n).incl).map_lie X Y }

@[simp]
theorem compactComplexInclusion_tmul (z : ℂ) (X : compactLieSubalgebra K n) :
    compactComplexInclusion K n (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] (X : RealLieAlgebra K n) := rfl

theorem compactComplexInclusion_injective : Function.Injective (compactComplexInclusion K n) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (compactLieSubalgebra K n).toSubmodule.subtype Subtype.val_injective

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual compact Lie generators in the ambient enveloping algebra. -/
def compactEnvelopingGenerator : CompactComplexLieAlgebra K n →ₗ⁅ℂ⁆ EnvelopingAlgebra K n :=
  (envelopingGenerator K n).comp (compactComplexInclusion K n)

/-- The complex unital subalgebra generated by the compact Lie generators. -/
def compactEnvelopingSubalgebra : Subalgebra ℂ (EnvelopingAlgebra K n) :=
  Algebra.adjoin ℂ (Set.range (compactEnvelopingGenerator K n))

@[simp]
theorem compactEnvelopingGenerator_tmul (z : ℂ) (X : compactLieSubalgebra K n) :
    compactEnvelopingGenerator K n (z ⊗ₜ[ℝ] X) =
      envelopingGenerator K n (z ⊗ₜ[ℝ] (X : RealLieAlgebra K n)) := rfl

theorem compactEnvelopingGenerator_mem (X : CompactComplexLieAlgebra K n) :
    compactEnvelopingGenerator K n X ∈ compactEnvelopingSubalgebra K n :=
  Algebra.subset_adjoin ⟨X, rfl⟩

theorem compactEnvelopingSubalgebra_le_iff (A : Subalgebra ℂ (EnvelopingAlgebra K n)) :
    compactEnvelopingSubalgebra K n ≤ A ↔
      ∀ X : CompactComplexLieAlgebra K n, compactEnvelopingGenerator K n X ∈ A := by
  rw [compactEnvelopingSubalgebra, Algebra.adjoin_le_iff]
  exact Set.range_subset_iff

end Langlands.Global.ArchimedeanGL
