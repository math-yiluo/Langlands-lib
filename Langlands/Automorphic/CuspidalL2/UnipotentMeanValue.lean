import Langlands.Global.ArchimedeanEnvelopingAction
import Langlands.Global.AdelicGL
import Mathlib.Analysis.Calculus.MeanValue

/-! # Mean value estimates along square-zero archimedean directions -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- The unit `1 + Z` for a square-zero archimedean matrix `Z`, with inverse `1 - Z`. -/
def squareZeroUnit (Z : ArchimedeanMatrix K n) (hZ : Z * Z = 0) : ArchimedeanGL K n where
  val := 1 + Z
  inv := 1 - Z
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, hZ, sub_zero, sub_add_cancel]
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, hZ, add_zero, add_sub_cancel_right]

omit [NumberField K] in
@[simp]
theorem squareZeroUnit_val (Z : ArchimedeanMatrix K n) (hZ : Z * Z = 0) :
    (squareZeroUnit Z hZ : ArchimedeanMatrix K n) = 1 + Z := rfl

omit [NumberField K] in
theorem smul_mul_smul_eq_zero {Z : ArchimedeanMatrix K n} (hZ : Z * Z = 0) (s : ℝ) :
    (s • Z) * (s • Z) = 0 := by
  rw [smul_mul_smul_comm, hZ, smul_zero]

/-- The actual infinite adelic element `1 + Z`. -/
def squareZeroElement (Z : ArchimedeanMatrix K n) (hZ : Z * Z = 0) : InfiniteAdelicGL K n :=
  (archimedeanGLCoordinates K n).symm (squareZeroUnit Z hZ)

/-- **Mean value estimate.** If `Z² = 0`, the variation of a smooth function along
`s ↦ x (1 + sZ)`, `0 ≤ s ≤ 1`, is bounded by a bound for its derivative in the
left-invariant direction `Z` along that segment. -/
theorem norm_sub_le_of_squareZero (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n)
    (Z : RealLieAlgebra K n)
    (hZ : realLieAlgebraToMatrix K n Z * realLieAlgebraToMatrix K n Z = 0) (M : ℝ)
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(smoothDifferential K n Z f).val
        (x * squareZeroElement (s • realLieAlgebraToMatrix K n Z)
          (smul_mul_smul_eq_zero hZ s))‖ ≤ M) :
    ‖f.val (x * squareZeroElement (realLieAlgebraToMatrix K n Z) hZ) - f.val x‖ ≤ M := by
  set Zm := realLieAlgebraToMatrix K n Z with hZm
  set xc : ArchimedeanGL K n := archimedeanGLCoordinates K n x with hxc
  let p : ℝ → ArchimedeanMatrix K n := fun s => (xc : ArchimedeanMatrix K n) * (1 + s • Zm)
  let h : ℝ → ℂ := fun s => coordinateExtension K n f (p s)
  have hp_unit (s : ℝ) : p s =
      ((xc * squareZeroUnit (s • Zm) (smul_mul_smul_eq_zero hZ s) : ArchimedeanGL K n) :
        ArchimedeanMatrix K n) := rfl
  have hh (s : ℝ) : h s = f.val (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s)) := by
    change coordinateExtension K n f (p s) = _
    rw [hp_unit, coordinateExtension_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hpderiv (s : ℝ) : HasDerivAt p ((xc : ArchimedeanMatrix K n) * Zm) s := by
    have h1 : HasDerivAt (fun s : ℝ => (1 : ArchimedeanMatrix K n) + s • Zm) Zm s := by
      simpa using ((hasDerivAt_id s).smul_const Zm).const_add (1 : ArchimedeanMatrix K n)
    have h2 := h1.const_mul (xc : ArchimedeanMatrix K n)
    simpa [p] using h2
  have hderiv (s : ℝ) : HasDerivAt h
      ((smoothDifferential K n Z f).val
        (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s))) s := by
    have hdiff : DifferentiableAt ℝ (coordinateExtension K n f) (p s) := by
      rw [hp_unit]
      exact (coordinateExtension_contDiffAt K n f _).differentiableAt (by simp)
    have hc : HasDerivAt h
        (fderiv ℝ (coordinateExtension K n f) (p s) ((xc : ArchimedeanMatrix K n) * Zm)) s :=
      hdiff.hasFDerivAt.comp_hasDerivAt s (hpderiv s)
    refine hc.congr_deriv ?_
    have hco : (archimedeanGLCoordinates K n
        (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s)) : ArchimedeanMatrix K n) =
        p s := by
      rw [hp_unit, map_mul, squareZeroElement, ContinuousMulEquiv.apply_symm_apply]
    rw [smoothDifferential_apply, hco]
    congr 1
    change (xc : ArchimedeanMatrix K n) * Zm = (xc : ArchimedeanMatrix K n) * (1 + s • Zm) * Zm
    rw [mul_assoc, add_mul, one_mul, smul_mul_assoc, hZ, smul_zero, add_zero]
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := h) (f' := fun s => (smoothDifferential K n Z f).val
        (x * squareZeroElement (s • Zm) (smul_mul_smul_eq_zero hZ s)))
    (a := 0) (b := 1) (C := M)
    (fun s _ => (hderiv s).hasDerivWithinAt) (fun s hs => hM s (Set.Ico_subset_Icc_self hs))
  have hb := hbound 1 (by simp)
  rw [hh, hh] at hb
  simp only [one_smul, zero_smul, sub_zero, mul_one] at hb
  have h0 : squareZeroElement (0 : ArchimedeanMatrix K n) (smul_mul_smul_eq_zero hZ 0 ▸
      by simp) = 1 := by
    apply (archimedeanGLCoordinates K n).injective
    rw [squareZeroElement, ContinuousMulEquiv.apply_symm_apply, map_one]
    apply Units.ext
    simp
  simpa [h0] using hb

end Langlands.Global.ArchimedeanGL
