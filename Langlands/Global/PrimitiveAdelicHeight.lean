import Langlands.Global.AdelicGL
import Langlands.Global.IdeleAbsoluteValue
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic

/-! # Normalized coordinate heights of actual primitive adelic vectors -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Actual vectors over the full number-field adele ring. -/
abbrev Vector := Fin n → Adeles F

/-- The coordinatewise principal rational-vector map. -/
def rational (v : Fin n → F) : Vector F n := fun i => diagonal F (v i)

/-- A primitive vector is in the actual adelic general-linear orbit of a nonzero
rational vector, as in Springer §1.8. -/
def IsPrimitive (x : Vector F n) : Prop :=
  ∃ (g : AdelicGL F n) (v : Fin n → F), v ≠ 0 ∧ x = g.val *ᵥ rational F n v

/-- The local maximum coordinate norm at a finite place. -/
def finiteNorm (x : Vector F n) (v : FinitePlace F) : ℝ :=
  ‖fun i : Fin n => finiteProjection F v (x i)‖

/-- The local maximum coordinate norm at an infinite place. -/
def infiniteNorm (x : Vector F n) (v : InfinitePlace F) : ℝ :=
  ‖fun i : Fin n => infiniteProjection F v (x i)‖

/-- The normalized height formula. Its use as a positive height is restricted to
primitive vectors; finite support is proved below. -/
def height (x : Vector F n) : ℝ :=
  (∏ v : InfinitePlace F, infiniteNorm F n x v ^ v.mult) *
    ∏ᶠ v : FinitePlace F, finiteNorm F n x v

/-- Primitive vectors admit a row whose product with the vector equals one. -/
theorem IsPrimitive.exists_row {x : Vector F n} (hx : IsPrimitive F n x) :
    ∃ y : Vector F n, ∑ i, y i * x i = 1 := by
  classical
  obtain ⟨g, v, hv, rfl⟩ := hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hj' : v j ≠ 0 := hj
  have hinv : (g⁻¹).val *ᵥ (g.val *ᵥ rational F n v) = rational F n v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  refine ⟨fun i => diagonal F (v j)⁻¹ * (g⁻¹) j i, ?_⟩
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change diagonal F (v j)⁻¹ * ((g⁻¹).val *ᵥ (g.val *ᵥ rational F n v)) j = 1
  rw [hinv]
  change diagonal F (v j)⁻¹ * diagonal F (v j) = 1
  rw [← map_mul, inv_mul_cancel₀ hj', map_one]

private theorem eventually_integral_norm (x : Vector F n) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i : Fin n, ‖finiteProjection F v (x i)‖ ≤ 1 := by
  have h : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i : Fin n, (x i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => (x i).2.property
  filter_upwards [h] with v hv
  intro i
  change ‖(x i).2 v‖ ≤ 1
  simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff] using hv i

/-- At almost every finite place the maximum norm of a primitive vector is one. -/
theorem IsPrimitive.eventually_finiteNorm_eq_one {x : Vector F n}
    (hx : IsPrimitive F n x) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite, finiteNorm F n x v = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_row F n
  filter_upwards [eventually_integral_norm F n x, eventually_integral_norm F n y] with v hxv hyv
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hxv
  · have heq : ∑ i, finiteProjection F v (y i) * finiteProjection F v (x i) = 1 := by
      simpa only [map_sum, map_mul, map_one] using congrArg (finiteProjection F v) hy
    have hle := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (norm_nonneg (fun i : Fin n => finiteProjection F v (x i)))
      (s := Finset.univ) (f := fun i => finiteProjection F v (y i) * finiteProjection F v (x i))
      (fun i _ => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hyv i) (norm_nonneg _)).trans
          (by simpa using norm_le_pi_norm (fun i : Fin n => finiteProjection F v (x i)) i))
    simpa only [heq, norm_one, finiteNorm] using hle

/-- The finite part of the height is an actual finite product on primitive vectors. -/
theorem IsPrimitive.hasFiniteMulSupport {x : Vector F n} (hx : IsPrimitive F n x) :
    (finiteNorm F n x).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (hx.eventually_finiteNorm_eq_one F n)

private theorem IsPrimitive.local_ne_zero {x : Vector F n} (hx : IsPrimitive F n x)
    {K : Type*} [CommRing K] [Nontrivial K] (f : Adeles F →+* K) :
    (fun i : Fin n => f (x i)) ≠ 0 := by
  obtain ⟨y, hy⟩ := hx.exists_row F n
  intro hz
  have hi (i : Fin n) : f (x i) = 0 := congrFun hz i
  have heq : (0 : K) = 1 := by
    simpa only [map_sum, map_mul, hi, mul_zero, Finset.sum_const_zero, map_one]
      using congrArg f hy
  exact zero_ne_one heq

/-- Every local maximum norm of a primitive vector is strictly positive. -/
theorem IsPrimitive.finiteNorm_pos {x : Vector F n} (hx : IsPrimitive F n x)
    (v : FinitePlace F) : 0 < finiteNorm F n x v :=
  norm_pos_iff.mpr (hx.local_ne_zero F n (finiteProjection F v))

/-- Every infinite local maximum norm of a primitive vector is strictly positive. -/
theorem IsPrimitive.infiniteNorm_pos {x : Vector F n} (hx : IsPrimitive F n x)
    (v : InfinitePlace F) : 0 < infiniteNorm F n x v :=
  norm_pos_iff.mpr (hx.local_ne_zero F n (infiniteProjection F v))

/-- The actual normalized product height is positive on primitive vectors. -/
theorem IsPrimitive.height_pos {x : Vector F n} (hx : IsPrimitive F n x) :
    0 < height F n x := by
  apply mul_pos
  · exact Finset.prod_pos fun v _ => pow_pos (hx.infiniteNorm_pos F n v) _
  · exact lt_of_le_of_ne (finprod_nonneg fun v => (hx.finiteNorm_pos F n v).le)
      (Ne.symm (finprod_ne_zero fun v => (hx.finiteNorm_pos F n v).ne'))

/-- The same normalized height as a positive real unit. -/
def positiveHeight (x : Vector F n) (hx : IsPrimitive F n x) : ℝ≥0ˣ :=
  Units.mk0 ⟨height F n x, (hx.height_pos F n).le⟩
    (by intro h; exact (hx.height_pos F n).ne' (congrArg NNReal.toReal h))

@[simp] theorem positiveHeight_val (x : Vector F n) (hx : IsPrimitive F n x) :
    ((positiveHeight F n x hx : ℝ≥0) : ℝ) = height F n x := rfl

/-- Finite local maximum norms scale by the actual local idele norm. -/
theorem finiteNorm_smul (t : Ideles F) (x : Vector F n) (v : FinitePlace F) :
    finiteNorm F n (t.val • x) v = ‖t.val.2 v‖ * finiteNorm F n x v := by
  simp only [finiteNorm, Pi.smul_apply, smul_eq_mul, map_mul]
  exact norm_smul (finiteProjection F v t.val)
    (fun i : Fin n => finiteProjection F v (x i))

/-- Infinite local maximum norms scale by the actual local idele norm. -/
theorem infiniteNorm_smul (t : Ideles F) (x : Vector F n) (v : InfinitePlace F) :
    infiniteNorm F n (t.val • x) v = ‖t.val.1 v‖ * infiniteNorm F n x v := by
  simp only [infiniteNorm, Pi.smul_apply, smul_eq_mul, map_mul]
  exact norm_smul (infiniteProjection F v t.val)
    (fun i : Fin n => infiniteProjection F v (x i))

/-- Scalar multiplication changes the height by the existing normalized idelic
absolute value, including the archimedean multiplicities. -/
theorem IsPrimitive.height_smul {x : Vector F n} (hx : IsPrimitive F n x)
    (t : Ideles F) :
    height F n (t.val • x) = ((IdeleAbsoluteValue.full F t : ℝ≥0) : ℝ) * height F n x := by
  have ht : (fun v : FinitePlace F => ‖t.val.2 v‖).HasFiniteMulSupport :=
    NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F t).2
  simp only [height, finiteNorm_smul, infiniteNorm_smul, mul_pow,
    Finset.prod_mul_distrib, finprod_mul_distrib ht (hx.hasFiniteMulSupport F n),
    IdeleAbsoluteValue.coe_full]
  ring

/-- Principal scalar multiplication preserves the normalized height. -/
theorem IsPrimitive.height_diagonal_smul {x : Vector F n} (hx : IsPrimitive F n x)
    (a : Fˣ) : height F n ((diagonalUnits F a).val • x) = height F n x := by
  rw [hx.height_smul F n, IdeleAbsoluteValue.full_diagonalUnits]
  simp

end Langlands.Global.PrimitiveAdelicHeight
