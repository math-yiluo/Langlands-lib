import Langlands.Global.ArchimedeanCompactLieAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Split central directions and the reduced archimedean Lie algebra -/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator
open NumberField

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- One real scalar at each real or complex infinite place. -/
abbrev SplitCenterCoordinates :=
  ({v : InfinitePlace K // v.IsReal} → ℝ) ×
    ({v : InfinitePlace K // v.IsComplex} → ℝ)

/-- Coordinatewise real part in the mixed archimedean algebra. -/
def mixedRealPart : mixedEmbedding.mixedSpace K →ₗ[ℝ] SplitCenterCoordinates K where
  toFun z := (z.1, fun v => (z.2 v).re)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Real scalars embedded at every infinite place. -/
def mixedRealScalar : SplitCenterCoordinates K →ₗ[ℝ] mixedEmbedding.mixedSpace K where
  toFun r := (r.1, fun v => (r.2 v : ℂ))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp]
theorem mixedRealPart_realScalar (r : SplitCenterCoordinates K) :
    mixedRealPart K (mixedRealScalar K r) = r := by
  ext <;> simp [mixedRealPart, mixedRealScalar]

@[simp]
theorem mixedRealPart_star (z : mixedEmbedding.mixedSpace K) :
    mixedRealPart K (star z) = mixedRealPart K z := by
  ext <;> simp [mixedRealPart]

/-- The real part of the matrix trace separately at every infinite place. -/
def realTrace : RealLieAlgebra K n →ₗ[ℝ] SplitCenterCoordinates K :=
  (mixedRealPart K).comp
    ((Matrix.traceLinearMap (Fin n) ℝ (mixedEmbedding.mixedSpace K)).comp
      (realLieAlgebraToMatrix K n).toLinearMap)

@[simp]
theorem realTrace_apply (X : RealLieAlgebra K n) :
    realTrace K n X = mixedRealPart K (Matrix.trace (realLieAlgebraToMatrix K n X)) :=
  rfl

@[simp]
theorem realTrace_lie (X Y : RealLieAlgebra K n) :
    realTrace K n ⁅X, Y⁆ = 0 := by
  rw [realTrace_apply, realLieAlgebraToMatrix_lie, Matrix.trace_sub,
    Matrix.trace_mul_comm, sub_self, map_zero]

@[simp]
theorem realTrace_star (X : RealLieAlgebra K n) :
    realTrace K n (star X) = realTrace K n X := by
  change mixedRealPart K (Matrix.trace (star (realLieAlgebraToMatrix K n X))) = _
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, mixedRealPart_star]
  rfl

/-- The complement of the real split central direction: real trace zero
at real places and purely imaginary trace at complex places. -/
def reducedLieSubalgebra : LieSubalgebra ℝ (RealLieAlgebra K n) :=
  { LinearMap.ker (realTrace K n) with
    lie_mem' := by
      intro X Y _ _
      exact realTrace_lie K n X Y }

@[simp]
theorem mem_reducedLieSubalgebra (X : RealLieAlgebra K n) :
    X ∈ reducedLieSubalgebra K n ↔ realTrace K n X = 0 := Iff.rfl

/-- Coordinate form of the reduced condition. -/
theorem mem_reducedLieSubalgebra_iff_coordinates (X : RealLieAlgebra K n) :
    X ∈ reducedLieSubalgebra K n ↔
      (∀ v, (Matrix.trace (realLieAlgebraToMatrix K n X)).1 v = 0) ∧
      (∀ v, ((Matrix.trace (realLieAlgebraToMatrix K n X)).2 v).re = 0) := by
  rw [mem_reducedLieSubalgebra]
  constructor
  · intro h
    exact ⟨fun v => congrArg (fun r : SplitCenterCoordinates K => r.1 v) h,
      fun v => congrArg (fun r : SplitCenterCoordinates K => r.2 v) h⟩
  · intro h
    exact Prod.ext (funext h.1) (funext h.2)

theorem compactLieSubalgebra_le_reduced :
    compactLieSubalgebra K n ≤ reducedLieSubalgebra K n := by
  intro X hX
  rw [mem_compactLieSubalgebra] at hX
  rw [mem_reducedLieSubalgebra]
  have h := congrArg (realTrace K n) hX
  rw [realTrace_star, map_neg] at h
  ext v
  · have hv := congrArg (fun r : SplitCenterCoordinates K => r.1 v) h
    change (realTrace K n X).1 v = -(realTrace K n X).1 v at hv
    change (realTrace K n X).1 v = 0
    linarith
  · have hv := congrArg (fun r : SplitCenterCoordinates K => r.2 v) h
    change (realTrace K n X).2 v = -(realTrace K n X).2 v at hv
    change (realTrace K n X).2 v = 0
    linarith

/-- The existing compact algebra as a subalgebra of the reduced algebra. -/
def compactToReduced :
    compactLieSubalgebra K n →ₗ⁅ℝ⁆ reducedLieSubalgebra K n :=
  LieSubalgebra.inclusion (compactLieSubalgebra_le_reduced K n)

/-- Real scalar diagonal matrices, with an independent scalar at each place. -/
def splitCenterScalar : SplitCenterCoordinates K →ₗ[ℝ] RealLieAlgebra K n :=
  (realLieAlgebraToMatrix K n).symm.toLinearMap.comp
    ((Matrix.scalarAlgHom (Fin n) ℝ).toLinearMap.comp (mixedRealScalar K))

@[simp]
theorem splitCenterScalar_matrix (r : SplitCenterCoordinates K) :
    realLieAlgebraToMatrix K n (splitCenterScalar K n r) =
      Matrix.scalar (Fin n) (mixedRealScalar K r) := rfl

theorem splitCenterScalar_lie (r : SplitCenterCoordinates K) (X : RealLieAlgebra K n) :
    ⁅splitCenterScalar K n r, X⁆ = 0 := by
  apply (realLieAlgebraToMatrix K n).injective
  rw [realLieAlgebraToMatrix_lie, splitCenterScalar_matrix, map_zero]
  exact sub_eq_zero.mpr (Matrix.scalar_commute _ (Commute.all _) _).eq

@[simp]
theorem realTrace_splitCenterScalar (r : SplitCenterCoordinates K) :
    realTrace K n (splitCenterScalar K n r) = (n : ℝ) • r := by
  rw [realTrace_apply, splitCenterScalar_matrix]
  rw [Matrix.scalar_apply, Matrix.trace_diagonal, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    map_smul, mixedRealPart_realScalar]

/-- The actual subspace of real scalar matrices; no positive rank is required. -/
def splitCenterSubmodule : Submodule ℝ (RealLieAlgebra K n) :=
  LinearMap.range (splitCenterScalar K n)

/-- The real scalar subspace is central, hence a Lie subalgebra. -/
def splitCenterLieSubalgebra : LieSubalgebra ℝ (RealLieAlgebra K n) :=
  { splitCenterSubmodule K n with
    lie_mem' := by
      rintro X Y ⟨r, rfl⟩ _
      rw [splitCenterScalar_lie]
      exact (splitCenterSubmodule K n).zero_mem }

theorem splitCenterLieSubalgebra_central (X : splitCenterLieSubalgebra K n)
    (Y : RealLieAlgebra K n) : ⁅(X : RealLieAlgebra K n), Y⁆ = 0 := by
  obtain ⟨r, hr⟩ := X.property
  rw [← hr, splitCenterScalar_lie]

/-- Normalized real trace, the scalar coordinate of the split central part. -/
def splitCenterCoordinate : RealLieAlgebra K n →ₗ[ℝ] SplitCenterCoordinates K :=
  (n : ℝ)⁻¹ • realTrace K n

@[simp]
theorem splitCenterCoordinate_scalar [NeZero n] (r : SplitCenterCoordinates K) :
    splitCenterCoordinate K n (splitCenterScalar K n r) = r := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  change (n : ℝ)⁻¹ • realTrace K n (splitCenterScalar K n r) = r
  rw [realTrace_splitCenterScalar, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem splitCenterScalar_injective [NeZero n] :
    Function.Injective (splitCenterScalar K n) :=
  Function.LeftInverse.injective (splitCenterCoordinate_scalar K n)

/-- Subtract the normalized real scalar trace to land in the reduced algebra. -/
def reducedProjection [NeZero n] :
    RealLieAlgebra K n →ₗ[ℝ] reducedLieSubalgebra K n :=
  (LinearMap.id - (splitCenterScalar K n).comp (splitCenterCoordinate K n)).codRestrict
    (reducedLieSubalgebra K n).toSubmodule (by
      intro X
      change realTrace K n (X - splitCenterScalar K n (splitCenterCoordinate K n X)) = 0
      rw [map_sub, realTrace_splitCenterScalar]
      have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      change realTrace K n X - (n : ℝ) • ((n : ℝ)⁻¹ • realTrace K n X) = 0
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul, sub_self])

@[simp]
theorem reducedProjection_apply [NeZero n] (X : RealLieAlgebra K n) :
    (reducedProjection K n X : RealLieAlgebra K n) =
      X - splitCenterScalar K n (splitCenterCoordinate K n X) := rfl

/-- The direct decomposition into real split central coordinates and the
reduced matrix Lie algebra, for positive rank. -/
def splitCenterDecomposition [NeZero n] :
    RealLieAlgebra K n ≃ₗ[ℝ] SplitCenterCoordinates K × reducedLieSubalgebra K n where
  toLinearMap := (splitCenterCoordinate K n).prod (reducedProjection K n)
  invFun p := splitCenterScalar K n p.1 + p.2
  left_inv X := by
    change splitCenterScalar K n (splitCenterCoordinate K n X) +
      (X - splitCenterScalar K n (splitCenterCoordinate K n X)) = X
    abel
  right_inv p := by
    have hp : realTrace K n (p.2 : RealLieAlgebra K n) = 0 := p.2.property
    have hp' : splitCenterCoordinate K n (p.2 : RealLieAlgebra K n) = 0 := by
      simp [splitCenterCoordinate, hp]
    apply Prod.ext
    · change splitCenterCoordinate K n
        (splitCenterScalar K n p.1 + (p.2 : RealLieAlgebra K n)) = p.1
      simp [hp']
    · apply Subtype.ext
      change splitCenterScalar K n p.1 + (p.2 : RealLieAlgebra K n) -
        splitCenterScalar K n (splitCenterCoordinate K n
          (splitCenterScalar K n p.1 + (p.2 : RealLieAlgebra K n))) = p.2
      simp [hp']

@[simp]
theorem splitCenterDecomposition_apply [NeZero n] (X : RealLieAlgebra K n) :
    splitCenterDecomposition K n X =
      (splitCenterCoordinate K n X, reducedProjection K n X) := rfl

@[simp]
theorem splitCenterDecomposition_symm_apply [NeZero n]
    (r : SplitCenterCoordinates K) (X : reducedLieSubalgebra K n) :
    (splitCenterDecomposition K n).symm (r, X) =
      splitCenterScalar K n r + (X : RealLieAlgebra K n) := rfl

/-- Complexification of the real trace complement, retaining imaginary
scalar directions at complex places. -/
abbrev ReducedComplexLieAlgebra := ℂ ⊗[ℝ] reducedLieSubalgebra K n

/-- The complexified reduced algebra inside the full complex Lie algebra. -/
def reducedComplexInclusion :
    ReducedComplexLieAlgebra K n →ₗ⁅ℂ⁆ ComplexLieAlgebra K n :=
  { (reducedLieSubalgebra K n).toSubmodule.subtype.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (reducedLieSubalgebra K n).incl).map_lie X Y }

@[simp]
theorem reducedComplexInclusion_tmul (z : ℂ) (X : reducedLieSubalgebra K n) :
    reducedComplexInclusion K n (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] (X : RealLieAlgebra K n) := rfl

theorem reducedComplexInclusion_injective :
    Function.Injective (reducedComplexInclusion K n) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (reducedLieSubalgebra K n).toSubmodule.subtype Subtype.val_injective

/-- The compact complex algebra maps into the reduced complex algebra. -/
def compactToReducedComplex :
    CompactComplexLieAlgebra K n →ₗ⁅ℂ⁆ ReducedComplexLieAlgebra K n :=
  { (compactToReduced K n).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (compactToReduced K n)).map_lie X Y }

@[simp]
theorem compactToReducedComplex_tmul (z : ℂ) (X : compactLieSubalgebra K n) :
    compactToReducedComplex K n (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] compactToReduced K n X := rfl

theorem reducedComplexInclusion_compact (X : CompactComplexLieAlgebra K n) :
    reducedComplexInclusion K n (compactToReducedComplex K n X) =
      compactComplexInclusion K n X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => rfl
  | add X Y hX hY => simp [hX, hY]

end Langlands.Global.ArchimedeanGL
