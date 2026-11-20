import Langlands.Global.RankinSelberg.ComplexTateCoordinateFourier
import Langlands.Global.RankinSelberg.ComplexTateProductHolomorphy
import Langlands.LocalFactor.Archimedean.ComplexTateGaussian
import Langlands.LocalFactor.Archimedean.Definitions

/-! # Common-strip reflection for a coordinate of the normalized Tate integral -/

noncomputable section

open Complex MeasureTheory
open scoped ENNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

/-- Reciprocal complex Tate Gamma factor for angular weight `m` and parameter `u`. -/
def gammaNormalizer (m : ℤ) (u : ℂ) : ℂ := (Gammaℂ (u + (m.natAbs : ℂ) / 2))⁻¹

/-- The product Tate integral multiplied by the reciprocal Gamma factors in all coordinates. -/
def normalizedZeta {ι : Type*} [Fintype ι] (F : (ι → ℂ) → ℂ) (m : ι → ℤ) (u : ι → ℂ) : ℂ :=
  (∏ i, gammaNormalizer (m i) (u i)) * zeta F m u

private def normalizedSlice (f : ℂ → ℂ) (m : ℤ) (u : ℂ) : ℂ :=
  gammaNormalizer m u * ∫ z, f z * additiveWeight m u z

private theorem scalar_zeta_eq (f : ℂ → ℂ) (m : ℤ) (u : ℂ) :
    Langlands.LocalFactor.ComplexTate.zeta f m u = 2 * ∫ z, f z * additiveWeight m u z := by
  unfold Langlands.LocalFactor.ComplexTate.zeta Langlands.LocalFactor.ComplexTate.measure
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z = 0 <;> simp [Langlands.LocalFactor.ComplexTate.integrand,
    Langlands.LocalFactor.ComplexTate.direction, additiveWeight, hz, mul_assoc]

private theorem gammaℂ_ne_zero (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    Gammaℂ (u + (m.natAbs : ℂ) / 2) ≠ 0 := by
  have hre : 0 < (u + (m.natAbs : ℂ) / 2).re := by
    simp only [add_re, div_ofNat_re, natCast_re]
    positivity
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hπ)))
    (Gamma_ne_zero_of_re_pos hre)

open Langlands.LocalFactor.ComplexTate (gaussian gaussSchwartz gaussSchwartz_apply
  integral_exp_mul_gaussian tate_identity zeta_const_mul zeta_gaussian traceChar)

private theorem normalizedSlice_fourier (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ}
    (hu₀ : 0 < u.re) (hu₁ : u.re < 1) :
    normalizedSlice (Langlands.LocalFactor.ComplexTate.fourier f) (-m) (1 - u) =
      I ^ m.natAbs * normalizedSlice f m u := by
  have huv : 0 < (1 - u).re := by simpa using sub_pos.mpr hu₁
  have hg : (gaussSchwartz m : ℂ → ℂ) = gaussian m := funext (gaussSchwartz_apply m)
  have hfg : (Langlands.LocalFactor.ComplexTate.fourier (gaussSchwartz m) : ℂ → ℂ) =
      fun y => I ^ m.natAbs * gaussian (-m) y := by
    funext y
    simpa only [Langlands.LocalFactor.ComplexTate.fourier_apply, hg, traceChar] using
      integral_exp_mul_gaussian m y
  have h := tate_identity f (gaussSchwartz m) m hu₀ hu₁
  simp only [hg, hfg, zeta_const_mul, zeta_gaussian m hu₀,
    zeta_gaussian (-m) huv, Int.natAbs_neg] at h
  simp only [scalar_zeta_eq] at h
  simp only [normalizedSlice, gammaNormalizer, Int.natAbs_neg]
  have hG₀ := gammaℂ_ne_zero m hu₀
  have hG₁ := gammaℂ_ne_zero m huv
  generalize Gammaℂ (u + (m.natAbs : ℂ) / 2) = G₀ at h hG₀ ⊢
  generalize Gammaℂ (1 - u + (m.natAbs : ℂ) / 2) = G₁ at h hG₁ ⊢
  field_simp
  linear_combination -h / 2

variable {n : ℕ}
local notation "V" => (Fin (n + 1) → ℂ)
local notation "Row" => (Fin n → ℂ)

private theorem zeta_eq_integral_slice (F : 𝓢(V, ℂ)) (i : Fin (n + 1))
    (m : Fin (n + 1) → ℤ) (u : V) (hu : ∀ j, 0 < (u j).re) :
    zeta F m u = ∫ x : Row, (∫ y : ℂ, coordinateSlice F i x y * additiveWeight (m i) (u i) y) *
      ∏ j : Fin n, additiveWeight (m (i.succAbove j)) (u (i.succAbove j)) (x j) := by
  let e : ℂ × Row ≃ᵐ V := (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) i).symm
  have he : MeasurePreserving e := (volume_preserving_piFinSuccAbove (fun _ => ℂ) i).symm _
  have hI : Integrable (fun p : ℂ × Row => integrand F m u (e p)) (volume.prod volume) :=
    ((he.integrable_comp_emb e.measurableEmbedding).mpr (integrable_integrand F m hu))
  rw [zeta, ← he.integral_comp' (f := e) (integrand F m u), Measure.volume_eq_prod, integral_prod_symm _ hI]
  apply integral_congr_ae
  filter_upwards with x
  have hi (y : ℂ) : integrand F m u (e (y, x)) =
      (coordinateSlice F i x y * additiveWeight (m i) (u i) y) *
        ∏ j : Fin n, additiveWeight (m (i.succAbove j)) (u (i.succAbove j)) (x j) := by
    change integrand F m u (i.insertNth y x) = _
    rw [integrand, Fin.prod_univ_succAbove _ i, coordinateSlice_apply, mul_assoc]
    simp
  simp_rw [hi, integral_mul_const]

private theorem normalizedZeta_eq_integral_slice (F : 𝓢(V, ℂ)) (i : Fin (n + 1))
    (m : Fin (n + 1) → ℤ) (u : V) (hu : ∀ j, 0 < (u j).re) :
    normalizedZeta F m u = (∏ j : Fin n, gammaNormalizer (m (i.succAbove j)) (u (i.succAbove j))) *
      ∫ x : Row, normalizedSlice (coordinateSlice F i x) (m i) (u i) *
        ∏ j : Fin n, additiveWeight (m (i.succAbove j)) (u (i.succAbove j)) (x j) := by
  rw [normalizedZeta, zeta_eq_integral_slice F i m u hu, Fin.prod_univ_succAbove _ i]
  simp_rw [normalizedSlice, mul_assoc, integral_const_mul]
  ring

/-- Reverse the angular weight in one coordinate. -/
def reflectedWeight {ι : Type*} [DecidableEq ι] (i : ι) (m : ι → ℤ) : ι → ℤ :=
  Function.update m i (-m i)

/-- Reflect the spectral parameter `u` to `1 - u` in one coordinate. -/
def reflectedParameter {ι : Type*} [DecidableEq ι] (i : ι) (u : ι → ℂ) : ι → ℂ :=
  Function.update u i (1 - u i)

theorem normalizedZeta_coordinateFourier (F : 𝓢(V, ℂ)) (i : Fin (n + 1))
    (m : Fin (n + 1) → ℤ) (u : V) (hu : ∀ j, 0 < (u j).re) (hi : (u i).re < 1) :
    normalizedZeta (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i u) =
      I ^ (m i).natAbs * normalizedZeta F m u := by
  have hu' (j : Fin (n + 1)) : 0 < (reflectedParameter i u j).re := by
    by_cases h : j = i
    · subst j
      simpa [reflectedParameter] using sub_pos.mpr hi
    · simpa [reflectedParameter, Function.update_of_ne h] using hu j
  rw [normalizedZeta_eq_integral_slice (coordinateFourier F i) i _ _ hu',
    normalizedZeta_eq_integral_slice F i m u hu]
  have hs (x : Row) : coordinateSlice (coordinateFourier F i) i x =
      Langlands.LocalFactor.ComplexTate.fourier (coordinateSlice F i x) := by
    ext y
    rw [coordinateSlice_apply, coordinateFourier_insertNth]
  simp only [reflectedWeight, reflectedParameter, Function.update_self,
    Function.update_of_ne (i.succAbove_ne _), hs, normalizedSlice_fourier _ _ (hu i) hi]
  simp_rw [mul_assoc, integral_const_mul]
  ring

/-- The normalized product Tate integrals satisfy the common-strip identity
under the positive trace transform in one coordinate. -/
def ComplexTateCoordinateReflectionStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (i : Fin (n + 1))
    (m : Fin (n + 1) → ℤ) (u : Fin (n + 1) → ℂ),
    (∀ j, 0 < (u j).re) → (u i).re < 1 →
      normalizedZeta (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i u) =
        I ^ (m i).natAbs * normalizedZeta F m u

theorem complexTateCoordinateReflection : ComplexTateCoordinateReflectionStatement :=
  fun _ F i m u hu hi => normalizedZeta_coordinateFourier F i m u hu hi

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
