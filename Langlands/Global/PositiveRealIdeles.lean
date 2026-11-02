import Langlands.Global.IdeleAbsoluteValue

/-!
# Positive real ideles in the actual adele ring

The same positive real is inserted at every infinite place, with finite part
equal to one. The paired Markdown records the source and normalization.
-/

noncomputable section

universe uF

namespace Langlands.Global.PositiveRealIdeles

open Langlands.Global
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NNReal

variable (F : Type uF) [Field F]

/-- The real subfield of an actual archimedean completion, in its chosen embedding. -/
def realEmbedding (v : InfinitePlace F) : ℝ →+* InfiniteCompletion F v := by
  classical
  exact if hv : IsReal v then
    (ringEquivRealOfIsReal hv).symm.toRingHom
  else
    (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)).symm.toRingHom.comp
      Complex.ofRealHom

@[simp]
theorem extensionEmbedding_realEmbedding (v : InfinitePlace F) (x : ℝ) :
    extensionEmbedding v (realEmbedding F v x) = (x : ℂ) := by
  classical
  unfold realEmbedding
  split
  · rename_i hv
    rw [← extensionEmbeddingOfIsReal_apply hv]
    exact congrArg Complex.ofReal ((ringEquivRealOfIsReal hv).apply_symm_apply x)
  · rename_i hv
    exact (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)).apply_symm_apply
      (x : ℂ)

theorem continuous_realEmbedding (v : InfinitePlace F) :
    Continuous (realEmbedding F v) := by
  classical
  unfold realEmbedding
  split
  · rename_i hv
    exact (isometryEquivRealOfIsReal hv).symm.continuous
  · rename_i hv
    exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)).symm.continuous.comp
      Complex.continuous_ofReal

@[simp]
theorem norm_realEmbedding (v : InfinitePlace F) (x : ℝ) :
    ‖realEmbedding F v x‖ = |x| := by
  have h := (isometry_extensionEmbedding v).norm_map_of_map_zero
    (map_zero (extensionEmbedding v)) (realEmbedding F v x)
  simpa only [extensionEmbedding_realEmbedding, Complex.norm_real, Real.norm_eq_abs] using h.symm

/-- Insert the same real number in every archimedean completion. -/
def infiniteRealEmbedding : ℝ →+* InfiniteAdeles F where
  toFun x v := realEmbedding F v x
  map_one' := funext fun v => map_one (realEmbedding F v)
  map_mul' x y := funext fun v => map_mul (realEmbedding F v) x y
  map_zero' := funext fun v => map_zero (realEmbedding F v)
  map_add' x y := funext fun v => map_add (realEmbedding F v) x y

theorem continuous_infiniteRealEmbedding : Continuous (infiniteRealEmbedding F) :=
  continuous_pi fun v => continuous_realEmbedding F v

/-- Positive real units, inserted equally in all archimedean components. -/
def infinite : ℝ≥0ˣ →ₜ* (InfiniteAdeles F)ˣ where
  toMonoidHom := Units.map
    ((infiniteRealEmbedding F).comp NNReal.toRealHom).toMonoidHom
  continuous_toFun :=
    ((continuous_infiniteRealEmbedding F).comp NNReal.continuous_coe).units_map _

variable [NumberField F]

/-- The actual idele with value `x` at all infinite places and `1` at finite places. -/
def full : ℝ≥0ˣ →ₜ* Ideles F :=
  (infiniteIdelesInclusion F).comp (infinite F)

@[simp]
theorem full_infinite_value (v : InfinitePlace F) (x : ℝ≥0ˣ) :
    (full F x).val.1 v = realEmbedding F v ((x : ℝ≥0) : ℝ) := rfl

@[simp]
theorem full_finite_value (v : FinitePlace F) (x : ℝ≥0ˣ) :
    (full F x).val.2 v = 1 := rfl

@[simp]
theorem finiteIdeleProjection_full (v : FinitePlace F) (x : ℝ≥0ˣ) :
    finiteIdeleProjection F v (full F x) = 1 := by
  apply Units.ext
  rfl

@[simp]
theorem extensionEmbedding_full (v : InfinitePlace F) (x : ℝ≥0ˣ) :
    extensionEmbedding v ((full F x).val.1 v) = (((x : ℝ≥0) : ℝ) : ℂ) :=
  extensionEmbedding_realEmbedding F v _

@[simp]
theorem norm_full_infinite_value (v : InfinitePlace F) (x : ℝ≥0ˣ) :
    ‖(full F x).val.1 v‖ = ((x : ℝ≥0) : ℝ) := by
  rw [full_infinite_value, norm_realEmbedding, abs_of_nonneg (NNReal.coe_nonneg _)]

theorem full_injective : Function.Injective (full F) := by
  classical
  let v : InfinitePlace F := Classical.arbitrary _
  intro x y h
  apply Units.ext
  apply NNReal.eq
  apply (realEmbedding F v).injective
  exact congrArg (fun z : Ideles F => z.val.1 v) h

/-- The normalized idelic norm retains the degree of the number field. -/
@[simp]
theorem absoluteValue_full (x : ℝ≥0ˣ) :
    IdeleAbsoluteValue.full F (full F x) = x ^ Module.finrank ℚ F := by
  apply Units.ext
  apply NNReal.eq
  rw [IdeleAbsoluteValue.coe_full]
  simp only [norm_full_infinite_value, full_finite_value, norm_one, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq]
  rfl

end Langlands.Global.PositiveRealIdeles
