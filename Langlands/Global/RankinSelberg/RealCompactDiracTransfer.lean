import Langlands.Global.RankinSelberg.RealCompactDiracIwasawa
import Langlands.Representation.Archimedean.KIntegralInvariance
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages

/-!
# Moving a translate from a principal-series vector to a test function

For a smooth principal-series vector `ξ` of signed-power characters with exponents `e`, a
continuous function `ψ` on `O(n)` and `h ∈ GL_n(ℝ)`,

`∫_{O(n)} ξ(k h) ψ(k) dk = ∫_{O(n)} ξ(k) Ψ(k h⁻¹) dk`,

where `Ψ = extension (dualExponent n e) ψ` is the extension of `ψ` with the dual exponents
`-e_l + (n-1)/2 - l`. For polynomial `ψ` the product `g ↦ ξ(g h) Ψ(g)` is smooth and transforms
by the modulus character, and the identity is the Library's `kIntegralInvariance`; the general
case follows by uniform approximation (Stone–Weierstrass).
-/

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped Matrix.Norms.Operator ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open PrincipalSeriesExtension GramFormula RealPrincipalSeriesDuality PartialJacquet
open RealPrincipalSeriesHilbert OrthogonalFinitePolynomial

attribute [local instance] measurableSpaceK RealPrincipalSeriesDuality.borelSpaceK

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## Equivariance of the extension under positive diagonal matrices -/

/-- Extensions of arbitrary profiles transform under positive diagonal and upper unipotent
matrices by `∏ₗ a_l^{s_l}`. -/
theorem extension_mul_left_pos (s : Fin n → ℂ) (φ : O → ℂ) (a : Fin n → ℝˣ)
    (ha : ∀ l, 0 < (a l : ℝ)) (u : upperUnipotent n ℝ) (g : G) :
    extension s φ ((Iwasawa.diagonalUnits a : G) * (u : G) * g) =
      (∏ l, (((a l : ℝ) : ℝ) : ℂ) ^ s l) * extension s φ g := by
  obtain ⟨a', u', k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  set b' : Mat := Matrix.diagonal (fun l => (a' l : ℝ)) * ((u' : G) : Mat) with hb'def
  set B : Mat := Matrix.diagonal (fun l => (a l : ℝ)) * ((u : G) : Mat) * b' with hBdef
  have hb' : b'.IsUpperTriangular := isUpperTriangular_diagonal_mul a' u'
  have hb'd : ∀ l, b' l l = a' l := diagonal_mul_apply_self a' u'
  have hB : B.IsUpperTriangular := (isUpperTriangular_diagonal_mul a u).mul hb'
  have hBd : ∀ l, B l l = a l * a' l := fun l => by
    rw [hBdef, upperTriangular_mul_apply_self (isUpperTriangular_diagonal_mul a u) hb',
      diagonal_mul_apply_self, hb'd]
  have hBne : ∀ l, B l l ≠ 0 := fun l => by
    rw [hBd]
    exact mul_ne_zero (a l).ne_zero (a' l).ne_zero
  have hb'ne : ∀ l, b' l l ≠ 0 := fun l => by
    rw [hb'd]
    exact (a' l).ne_zero
  have hx : (((Iwasawa.diagonalUnits a : G) * (u : G) *
      ((Iwasawa.diagonalUnits a' : G) * (u' : G) * k) : G) : Mat) = B * (k : Mat) := by
    rw [hBdef, hb'def]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rfl
  rw [extension_eq _ φ hB hBne hk hx, extension_eq _ φ hb' hb'ne hk (by rfl)]
  have hsign : signDiagonal (fun i => B i i) = signDiagonal (fun i => b' i i) := by
    apply Subtype.ext
    change (Matrix.diagonal fun i => signReal (B i i)) = Matrix.diagonal fun i => signReal (b' i i)
    congr 1
    funext i
    rw [hBd, hb'd, signReal_mul (a i).ne_zero (a' i).ne_zero]
    simp [signReal, ha i]
  rw [hsign]
  have hprod : (∏ l : Fin n, ((|B l l| : ℝ) : ℂ) ^ s l) =
      (∏ l : Fin n, (((a l : ℝ) : ℝ) : ℂ) ^ s l) * ∏ l : Fin n, ((|b' l l| : ℝ) : ℂ) ^ s l := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hBd, hb'd, abs_mul, abs_of_pos (ha l), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha l).le (abs_nonneg _)]
  rw [hprod, mul_assoc]

/-! ## The dual exponents and modulus equivariance -/

/-- The exponents `-e_l + (n-1)/2 - l` of the dual principal series. -/
def dualExponent (n : ℕ) (e : ℕ → ℂ) : Fin n → ℂ := shiftedExponent n fun l => -e l

theorem isModulusEquivariant_translate_mul_extension {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) {ξ : G → ℂ} (hξ : ξ ∈ principalSeries ℝ n χ) (h : G)
    (φ : O → ℂ) :
    IsModulusEquivariant fun g => ξ (g * h) * extension (dualExponent n e) φ g := by
  intro x u g
  rw [matrixExpUnit_diagonal]
  set a : Fin n → ℝˣ := fun i => Units.mk0 (Real.exp (x i)) (Real.exp_pos _).ne' with ha
  have hpos : ∀ l, 0 < (a l : ℝ) := fun l => Real.exp_pos _
  have hξ2 := ((mem_principalSeries_iff ℝ n χ ξ).mp hξ).2 a u (g * h)
  simp only [mul_assoc] at hξ2 ⊢
  rw [hξ2, ← mul_assoc (Iwasawa.diagonalUnits a : G), extension_mul_left_pos _ φ a hpos]
  have hsign : principalSeriesCharacter ℝ n χ (fun l => signUnit (a l)) = 1 := by
    unfold principalSeriesCharacter
    refine Finset.prod_eq_one fun l _ => ?_
    have h1 : signUnit (a l) = 1 := by simp [signUnit, hpos l]
    show χ l (signUnit (a l)) * _ = 1
    simp [h1, hχ.one]
  have hchar := principalSeriesCharacter_eq e hχ.eq a
  rw [hsign, mul_one] at hchar
  rw [hchar]
  have key : (∏ l : Fin n, ((|(a l : ℝ)| : ℝ) : ℂ) ^ shiftedExponent n e l) *
      ∏ l : Fin n, (((a l : ℝ) : ℝ) : ℂ) ^ dualExponent n e l =
      Complex.exp (∑ i, modulusExponent n i * (x i : ℂ)) := by
    rw [← Finset.prod_mul_distrib, Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hal : (a l : ℝ) = Real.exp (x l) := rfl
    rw [abs_of_pos (hpos l), hal, ofReal_exp_cpow, ofReal_exp_cpow, ← Complex.exp_add]
    congr 1
    simp only [dualExponent, shiftedExponent, modulusExponent]
    ring
  rw [← key]
  ring

/-! ## The Haar measures on `O(n)` -/

theorem map_haarOrthogonal :
    (haarOrthogonal n).map (orthogonalCompactEquiv n) = haarK n := by
  have : (Measure.map (orthogonalCompactEquiv n) (haarOrthogonal n)).IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure _ (orthogonalCompactEquiv n).toMonoidHom
      continuous_orthogonalCompactEquiv (orthogonalCompactEquiv n).surjective
  have : IsProbabilityMeasure (Measure.map (orthogonalCompactEquiv n) (haarOrthogonal n)) :=
    inferInstance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- `GL_n(ℝ)`-invariance of the `O(n)`-integral, for the Haar probability measure on the
orthogonal matrices. -/
theorem integral_haarOrthogonal_mul {φ : G → ℂ} (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ)
    (hmod : IsModulusEquivariant φ) (g : G) :
    ∫ κ, φ (Unitary.toUnits κ * g) ∂haarOrthogonal n =
      ∫ κ, φ (Unitary.toUnits κ) ∂haarOrthogonal n := by
  have h := kIntegralInvariance n φ hφ hmod g
  rw [← map_haarOrthogonal] at h
  have hc : Continuous φ := hφ.continuous
  have hm := continuous_orthogonalCompactEquiv.measurable.aemeasurable (μ := haarOrthogonal n)
  have h1 : AEStronglyMeasurable (fun k : unitaryCompact ℝ n => φ ((k : G) * g))
      (Measure.map (orthogonalCompactEquiv n) (haarOrthogonal n)) :=
    (hc.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun k : unitaryCompact ℝ n => φ (k : G))
      (Measure.map (orthogonalCompactEquiv n) (haarOrthogonal n)) :=
    (hc.comp continuous_subtype_val).aestronglyMeasurable
  rw [integral_map hm h1, integral_map hm h2] at h
  exact h

/-! ## Polynomial profiles and approximation -/

theorem exists_mvPolynomial_of_mem_polynomialStar {p : C(O, ℂ)} (hp : p ∈ polynomialStar n) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ κ : O,
      p κ = MvPolynomial.eval (fun ij => ((κ : Mat) ij.1 ij.2 : ℂ)) P := by
  rw [← StarSubalgebra.mem_toSubalgebra, polynomialStar_toSubalgebra] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact ⟨MvPolynomial.X ij, fun κ => by simp⟩
  | algebraMap r => exact ⟨MvPolynomial.C r, fun κ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun κ => by simp [hP, hQ]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P * Q, fun κ => by simp [hP, hQ]⟩

theorem exists_polynomialStar_near (ψ : C(O, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ polynomialStar n, ‖ψ - p‖ < ε := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (polynomialStar n) polynomialStar_separatesPoints
  have hmem : ψ ∈ (polynomialStar n).topologicalClosure := by
    rw [htop]
    exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hmem
  obtain ⟨p, hp, hd⟩ := Metric.mem_closure_iff.1 hmem ε hε
  exact ⟨p, hp, by rwa [dist_eq_norm] at hd⟩

/-! ## The transfer identity -/

theorem integral_translate_eq_of_polynomial {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) {ξ : G → ℂ} (hξ : ξ ∈ principalSeries ℝ n χ) (h : G)
    {p : C(O, ℂ)} (hp : p ∈ polynomialStar n) :
    ∫ κ, ξ (Unitary.toUnits κ * h) * p κ ∂haarOrthogonal n =
      ∫ κ, ξ (Unitary.toUnits κ) * extension (dualExponent n e) p (Unitary.toUnits κ * h⁻¹)
        ∂haarOrthogonal n := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialStar hp
  have hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (fun g => ξ (g * h) * extension (dualExponent n e) p g) :=
    contMDiff_mul_fun (rightTranslation_mem_principalSeries χ hξ h).1
      (contMDiff_extension _ hP)
  have hmod := isModulusEquivariant_translate_mul_extension hχ hξ h p
  have hI := integral_haarOrthogonal_mul hF hmod h⁻¹
  simp only [inv_mul_cancel_right, extension_unitary] at hI
  exact hI.symm

theorem continuous_extension_translate (s : Fin n → ℂ) (φ : C(O, ℂ)) (h : G) :
    Continuous fun κ : O => extension s φ (Unitary.toUnits κ * h) := by
  have hg : Continuous fun κ : O => Unitary.toUnits κ * h :=
    continuous_unitary_toUnits.mul continuous_const
  simp only [extension_eq_multiplier]
  exact ((continuous_multiplier s).comp hg).mul
    (φ.continuous.comp (RealCartanCompactSupport.continuous_signedOrthogonalPart.comp hg))

/-- **Transfer of a translate.** For a smooth principal-series vector `ξ` of signed-power
characters, a continuous `ψ` on `O(n)` and `h ∈ GL_n(ℝ)`,
`∫ ξ(k h) ψ(k) dk = ∫ ξ(k) Ψ(k h⁻¹) dk` with `Ψ` the extension of `ψ` with the dual
exponents. -/
theorem integral_translate_eq {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) {ξ : G → ℂ} (hξ : ξ ∈ principalSeries ℝ n χ) (h : G)
    (ψ : C(O, ℂ)) :
    ∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂haarOrthogonal n =
      ∫ κ, ξ (Unitary.toUnits κ) * extension (dualExponent n e) ψ (Unitary.toUnits κ * h⁻¹)
        ∂haarOrthogonal n := by
  set μ := haarOrthogonal n
  set s := dualExponent n e
  have hcξ : Continuous ξ := hξ.1.continuous
  have hc1 : Continuous fun κ : O => ξ (Unitary.toUnits κ * h) :=
    hcξ.comp (continuous_unitary_toUnits.mul continuous_const)
  have hc2 : Continuous fun κ : O => ξ (Unitary.toUnits κ) * multiplier s (Unitary.toUnits κ * h⁻¹) :=
    (hcξ.comp continuous_unitary_toUnits).mul
      ((continuous_multiplier s).comp (continuous_unitary_toUnits.mul continuous_const))
  obtain ⟨C₁, hC₁⟩ := isCompact_univ.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_univ.exists_bound_of_continuousOn hc2.continuousOn
  have hA : ∀ φ : C(O, ℂ), Integrable (fun κ => ξ (Unitary.toUnits κ * h) * φ κ) μ :=
    fun φ => integrable_of_continuous μ (hc1.mul φ.continuous)
  have hB : ∀ φ : C(O, ℂ), Integrable
      (fun κ => ξ (Unitary.toUnits κ) * extension s φ (Unitary.toUnits κ * h⁻¹)) μ :=
    fun φ => integrable_of_continuous μ ((hcξ.comp continuous_unitary_toUnits).mul
      (continuous_extension_translate s φ h⁻¹))
  have hμ : μ.real Set.univ = 1 := by simp [μ]
  have key : ∀ ε > 0, ‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
      ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ ≤
        (C₁ + C₂) * ε := by
    intro ε hε
    obtain ⟨p, hp, hpε⟩ := exists_polynomialStar_near ψ hε
    have hpoly : ∫ κ, ξ (Unitary.toUnits κ * h) * p κ ∂μ =
        ∫ κ, ξ (Unitary.toUnits κ) * extension s p (Unitary.toUnits κ * h⁻¹) ∂μ :=
      integral_translate_eq_of_polynomial hχ hξ h hp
    have h1 : ‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
        ∫ κ, ξ (Unitary.toUnits κ * h) * p κ ∂μ‖ ≤ C₁ * ε := by
      rw [← integral_sub (hA ψ) (hA p)]
      have hb : ∀ κ : O, ‖ξ (Unitary.toUnits κ * h) * ψ κ - ξ (Unitary.toUnits κ * h) * p κ‖ ≤
          C₁ * ε := by
        intro κ
        rw [← mul_sub, norm_mul]
        have h2 : ‖ψ κ - p κ‖ ≤ ε := by
          have := (ψ - p).norm_coe_le_norm κ
          exact le_trans (by simpa using this) hpε.le
        exact mul_le_mul (hC₁ κ (Set.mem_univ _)) h2 (norm_nonneg _)
          ((norm_nonneg _).trans (hC₁ κ (Set.mem_univ _)))
      have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
      rwa [hμ, mul_one] at this
    have h2 : ‖(∫ κ, ξ (Unitary.toUnits κ) * extension s p (Unitary.toUnits κ * h⁻¹) ∂μ) -
        ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ ≤ C₂ * ε := by
      rw [← integral_sub (hB p) (hB ψ)]
      have hb : ∀ κ : O, ‖ξ (Unitary.toUnits κ) * extension s p (Unitary.toUnits κ * h⁻¹) -
          ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹)‖ ≤ C₂ * ε := by
        intro κ
        simp only [extension_eq_multiplier]
        set g := Unitary.toUnits κ * h⁻¹
        have he : ξ (Unitary.toUnits κ) * (multiplier s g * p (signedOrthogonalPart g)) -
            ξ (Unitary.toUnits κ) * (multiplier s g * ψ (signedOrthogonalPart g)) =
            (ξ (Unitary.toUnits κ) * multiplier s g) *
              (p (signedOrthogonalPart g) - ψ (signedOrthogonalPart g)) := by ring
        rw [he, norm_mul]
        have h3 : ‖p (signedOrthogonalPart g) - ψ (signedOrthogonalPart g)‖ ≤ ε := by
          have := (ψ - p).norm_coe_le_norm (signedOrthogonalPart g)
          rw [norm_sub_rev]
          exact le_trans (by simpa using this) hpε.le
        exact mul_le_mul (hC₂ κ (Set.mem_univ _)) h3 (norm_nonneg _)
          ((norm_nonneg _).trans (hC₂ κ (Set.mem_univ _)))
      have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
      rwa [hμ, mul_one] at this
    calc _ = ‖((∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
            ∫ κ, ξ (Unitary.toUnits κ * h) * p κ ∂μ) +
          ((∫ κ, ξ (Unitary.toUnits κ) * extension s p (Unitary.toUnits κ * h⁻¹) ∂μ) -
            ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ)‖ := by
          rw [hpoly]
          congr 1
          abel
      _ ≤ C₁ * ε + C₂ * ε := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = (C₁ + C₂) * ε := by ring
  have hzero : ‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
      ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ = 0 := by
    have hC : 0 ≤ C₁ + C₂ := by
      have a1 := (norm_nonneg _).trans (hC₁ 1 (Set.mem_univ _))
      have a2 := (norm_nonneg _).trans (hC₂ 1 (Set.mem_univ _))
      linarith
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hpos
    push Not at hpos
    have hε : 0 < ‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
        ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ /
          (2 * (C₁ + C₂ + 1)) := by positivity
    have := key _ hε
    have h4 : (C₁ + C₂) * (‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
        ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ /
          (2 * (C₁ + C₂ + 1))) < ‖(∫ κ, ξ (Unitary.toUnits κ * h) * ψ κ ∂μ) -
        ∫ κ, ξ (Unitary.toUnits κ) * extension s ψ (Unitary.toUnits κ * h⁻¹) ∂μ‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)


end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
