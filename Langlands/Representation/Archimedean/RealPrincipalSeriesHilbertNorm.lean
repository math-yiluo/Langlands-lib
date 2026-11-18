import Langlands.Representation.Archimedean.KIntegralInvariance
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Bounds for real principal-series translation in the compact Hilbert norm -/

noncomputable section

open scoped Manifold ContDiff ComplexConjugate InnerProductSpace Matrix.Norms.Operator
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open RealJacquetFrobenius RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n

/-- The smooth principal series with the given full diagonal exponents and parities. -/
abbrev PrincipalSeries (a : Fin n → ℂ) (e : Fin n → Fin 2) :=
  ↥(principalSeries ℝ n (posChar a e))

variable (a : Fin n → ℂ) (e : Fin n → Fin 2)

/-- The algebraic right translation action on the smooth principal series. -/
def translation : Representation ℂ GL (PrincipalSeries a e) where
  toFun g :=
    { toFun := fun f => ⟨_, rightTranslation_mem_principalSeries (posChar a e) f.2 g⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext <| funext fun x => congrArg f.1 (mul_one x)
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (by
    funext x
    change f.1 (x * (g * h)) = f.1 ((x * g) * h)
    rw [mul_assoc])

@[simp]
theorem translation_apply (g x : GL) (f : PrincipalSeries a e) :
    (translation a e g f).1 x = f.1 (x * g) :=
  rfl

/-- Restrict a smooth principal-series function to the compact group. -/
def compactRestriction : PrincipalSeries a e →ₗ[ℂ] C(K, ℂ) where
  toFun f := ⟨fun k => f.1 (k : GL), f.2.1.continuous.comp continuous_subtype_val⟩
  map_add' _ _ := ContinuousMap.ext fun _ => rfl
  map_smul' _ _ := ContinuousMap.ext fun _ => rfl

/-- Restriction to the compact group, viewed in `L²(O(n))` for normalized Haar measure. -/
def restrictToL2 : PrincipalSeries a e →ₗ[ℂ] Lp ℂ 2 (haarK n) :=
  (ContinuousMap.toLp 2 (haarK n) ℂ).toLinearMap.comp (compactRestriction a e)

theorem restrictToL2_injective : Function.Injective (restrictToL2 a e) := by
  intro f h hfh
  have he := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (haarK n) hfh
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2 h.2 fun k hk => ?_
  exact ContinuousMap.congr_fun he ⟨k, hk⟩

theorem restrictToL2_norm_sq (f : PrincipalSeries a e) :
    ‖restrictToL2 a e f‖ ^ 2 = ∫ k : K, ‖f.1 (k : GL)‖ ^ 2 ∂haarK n := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (μ := haarK n) (𝕜 := ℂ)
    (compactRestriction a e f)
  calc
    ‖restrictToL2 a e f‖ ^ 2 =
        (∫ k, ⟪restrictToL2 a e f k, restrictToL2 a e f k⟫_ℂ ∂haarK n).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ k : K, ((‖f.1 (k : GL)‖ ^ 2 : ℝ) : ℂ) ∂haarK n).re := by
      apply congrArg Complex.re
      apply integral_congr_ae
      filter_upwards [h] with k hk
      change restrictToL2 a e f k = f.1 (k : GL) at hk
      rw [hk, inner_self_eq_norm_sq_to_K]
      change (‖f.1 (k : GL)‖ : ℂ) ^ 2 = ((‖f.1 (k : GL)‖ ^ 2 : ℝ) : ℂ)
      exact (Complex.ofReal_pow _ _).symm
    _ = _ := by
      have hcoe := integral_ofReal (μ := haarK n) (𝕜 := ℂ) (f := fun k : K => ‖f.1 (k : GL)‖ ^ 2)
      simpa only [Complex.ofReal_re] using! congrArg Complex.re hcoe

private def weightExponent (i : Fin n) : ℂ :=
  ((modulusExponent n i).re / 2 - (a i).re : ℝ)

private def weight : GL → ℂ :=
  frobFun (Representation.trivial ℂ (Matrix.unitaryGroup (Fin n) ℝ) ℂ)
    LinearMap.id (weightExponent a) (fun _ => 0) 1

private theorem weight_sign (j : Fin n) (z : ℂ) :
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (Representation.trivial ℂ (Matrix.unitaryGroup (Fin n) ℝ) ℂ (signReflection n j) z) =
      (-1) ^ ((0 : Fin 2).val) * z := by
  simp

private theorem contMDiff_weight : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (weight a) := by
  apply contMDiff_of_contDiffOn
    (ψ := unitsExtension (weight a)) (φ := weight a)
  · intro y hy
    apply (contDiffAt_unitsExtension_frobFun (a := weightExponent a)
      (weight_sign (n := n)) (P := 1) (v := (1 : ℂ)) ?_ hy).contDiffWithinAt
    intro k
    simp [polyEval]
  · intro g
    exact (unitsExtension_val _ g).symm

private theorem weight_ne_zero (g : GL) : weight a g ≠ 0 := by
  have hb := iw_spec g
  simpa [weight, frobFun, diagChar] using
    (Finset.prod_ne_zero_iff.mpr fun i _ =>
      charFun_ne_zero (0 : Fin 2) (weightExponent a i) (diag_ne_zero hb.1 hb.2.1 i))

private theorem weight_apply_compact (k : K) : weight a (k : GL) = 1 := by
  have hk : ((k : GL) : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ := k.2
  have he : ((k : GL) : Matrix (Fin n) (Fin n) ℝ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) * ((k : GL) : Matrix (Fin n) (Fin n) ℝ) := (one_mul _).symm
  rw [weight, frobFun_eq (weight_sign (n := n)) Matrix.blockTriangular_one hk he]
  simp [diagChar_one]

private theorem principalSeriesCharacter_exp (b : Fin n → ℂ) (d : Fin n → Fin 2)
    (x : Fin n → ℝ) :
    principalSeriesCharacter ℝ n (posChar b d)
        (fun i => Units.mk0 (Real.exp (x i)) (Real.exp_pos _).ne') =
      Complex.exp (∑ i, (x i : ℂ) * b i) := by
  rw [principalSeriesCharacter_eq, ← Langlands.GeneralLinear.Iwasawa.diagonalUnits_val,
    ← matrixExpUnit_diagonal, matrixExpUnit_val, diagChar_exp_diagonal]

private theorem weighted_function_left (f : PrincipalSeries a e) (x : Fin n → ℝ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℝ) (g : GL) :
    let b := matrixExpUnit n (Matrix.diagonal x) * (u : GL) * g
    weight a b * f.1 b = Complex.exp (∑ i, (x i : ℂ) * (weightExponent a i + a i)) *
      (weight a g * f.1 g) := by
  dsimp only
  rw [matrixExpUnit_diagonal, weight, frobFun_left (weight_sign (n := n)), f.2.2,
    principalSeriesCharacter_exp, principalSeriesCharacter_exp]
  simp_rw [mul_add, Finset.sum_add_distrib, Complex.exp_add]
  ring

private theorem weighted_norm_modulus (f : PrincipalSeries a e) :
    IsModulusEquivariant (fun g => ((‖weight a g * f.1 g‖ ^ 2 : ℝ) : ℂ)) := by
  intro x u g
  let s : ℂ := ∑ i, (x i : ℂ) * (weightExponent a i + a i)
  let t : ℝ := ∑ i, (modulusExponent n i).re * x i
  have hs : 2 * s.re = t := by
    dsimp only [s, t]
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      weightExponent, zero_mul, sub_zero]
    ring
  have ht : (t : ℂ) = ∑ i, modulusExponent n i * (x i : ℂ) := by
    dsimp only [t]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [modulusExponent]
  have hnorm : ‖Complex.exp s‖ ^ 2 = Real.exp t := by
    rw [Complex.norm_exp, pow_two, ← Real.exp_add, ← two_mul, hs]
  dsimp only
  rw [weighted_function_left, norm_mul, mul_pow, hnorm, Complex.ofReal_mul, Complex.ofReal_exp, ht]

private theorem contMDiff_weighted_norm (f : PrincipalSeries a e) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun g => ((‖weight a g * f.1 g‖ ^ 2 : ℝ) : ℂ)) := by
  have hv := contMDiff_mul_fun (contMDiff_weight a) f.2.1
  have hc := Complex.conjCLE.toContinuousLinearMap.contDiff.contMDiff.comp hv
  have hv' : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (fun g => conj (weight a g * f.1 g)) := hc
  have hs (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.conj_mul]
    exact (Complex.ofReal_pow _ _).symm
  simpa only [hs] using contMDiff_mul_fun hv' hv

private theorem weighted_sq_integral (f : PrincipalSeries a e) (g : GL) :
    (∫ k : K, ‖weight a ((k : GL) * g) * f.1 ((k : GL) * g)‖ ^ 2 ∂haarK n) =
      ‖restrictToL2 a e f‖ ^ 2 := by
  have h := KIntegralInvariance.integral_mul_eq (contMDiff_weighted_norm a e f)
    (weighted_norm_modulus a e f) g
  rw [restrictToL2_norm_sq]
  simp only [weight_apply_compact, one_mul] at h
  have h₁ := integral_ofReal (μ := haarK n) (𝕜 := ℂ)
    (f := fun k : K => ‖weight a ((k : GL) * g) * f.1 ((k : GL) * g)‖ ^ 2)
  have h₂ := integral_ofReal (μ := haarK n) (𝕜 := ℂ) (f := fun k : K => ‖f.1 (k : GL)‖ ^ 2)
  apply Complex.ofReal_injective
  exact h₁.symm.trans (h.trans h₂)

/-- On a compact set of group elements, right translations have a common bound in
the `L²` norm of the compact restriction. -/
theorem exists_norm_translation_le {S : Set GL} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ S, ∀ f : PrincipalSeries a e,
      ‖restrictToL2 a e (translation a e g f)‖ ≤ C * ‖restrictToL2 a e f‖ := by
  let q : K × GL → ℝ := fun p => ‖weight a ((p.1 : GL) * p.2)‖⁻¹
  have hcont : Continuous q :=
    ((contMDiff_weight a).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).norm.inv₀
        fun p => norm_ne_zero_iff.mpr (weight_ne_zero a ((p.1 : GL) * p.2))
  obtain ⟨B, hB⟩ := (isCompact_univ.prod hS).exists_bound_of_continuousOn hcont.continuousOn
  let C := max 0 B
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, fun g hg f => ?_⟩
  have hb (k : K) : ‖f.1 ((k : GL) * g)‖ ≤
      C * ‖weight a ((k : GL) * g) * f.1 ((k : GL) * g)‖ := by
    have hq : q (k, g) ≤ C :=
      (le_abs_self _).trans ((hB (k, g) ⟨Set.mem_univ _, hg⟩).trans (le_max_right _ _))
    have hpos : 0 < ‖weight a ((k : GL) * g)‖ := norm_pos_iff.mpr (weight_ne_zero a _)
    have hc : 1 ≤ C * ‖weight a ((k : GL) * g)‖ := (inv_le_iff_one_le_mul₀ hpos).mp hq
    rw [norm_mul, ← mul_assoc]
    exact le_mul_of_one_le_left (norm_nonneg _) hc
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [restrictToL2_norm_sq, mul_pow, ← weighted_sq_integral a e f g, ← integral_const_mul]
  apply integral_mono
  · exact ((translation a e g f).2.1.continuous.comp continuous_subtype_val).norm.pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hwf : Continuous (fun k : K => weight a ((k : GL) * g) * f.1 ((k : GL) * g)) :=
      ((contMDiff_weight a).continuous.mul f.2.1.continuous).comp
        (continuous_subtype_val.mul continuous_const)
    exact ((hwf.norm.pow 2).const_mul _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro k
    change ‖f.1 ((k : GL) * g)‖ ^ 2 ≤ C ^ 2 *
      ‖weight a ((k : GL) * g) * f.1 ((k : GL) * g)‖ ^ 2
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hb k)

end Langlands.Archimedean.RealPrincipalSeriesHilbert
