import Langlands.Global.RankinSelberg.EqualAnalyticIdeles
import Langlands.Global.RankinSelberg.EqualAnalyticExpHom

/-! # Idele class characters on `GL_1(𝔸)`

For an idele class character `χ` and `z ∈ GL_1(𝔸)` write `χ(z) = χ(det z)` (`ideleChar`).

* `χ` is a continuous homomorphism, trivial on `F^×`.
* **Dichotomy** (`ideleChar_dichotomy`): either `χ(z) = |z|^w` for some `w : ℂ` and all `z`, or
  `χ(z₀) ≠ 1` for some `z₀` of norm one. If `χ` is trivial on norm-one ideles, then
  `y ↦ χ(normScale y)` is a continuous exponential, hence `exp (w y)`.
* **Vanishing** (`integral_ideleChar_mul_eq_zero`): in the second case,
  `∫_(D₁) χ(a) u(log |a|) d^×a = 0` for every `u`, by translating by `z₀`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance ideleCharSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance ideleCharSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- The value `χ(det z)` of an idele class character at `z ∈ GL_1(𝔸)`. -/
def ideleChar (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (z : Points F 1) : ℂ :=
  (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ)

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)

theorem ideleOf_mul (a b : Points F 1) : ideleOf F (a * b) = ideleOf F a * ideleOf F b := by
  simp only [ideleOf, map_mul]

theorem ideleOf_one : ideleOf F 1 = 1 := by
  simp only [ideleOf, map_one]

theorem continuous_ideleOf : Continuous (ideleOf F) :=
  (AdelicGL.determinant F 1).continuous.comp (e 1).continuous

theorem ideleChar_mul (a b : Points F 1) :
    ideleChar F χ (a * b) = ideleChar F χ a * ideleChar F χ b := by
  simp only [ideleChar, ideleOf_mul, map_mul, Units.val_mul]

theorem ideleChar_one : ideleChar F χ 1 = 1 := by
  simp only [ideleChar, ideleOf_one, map_one, Units.val_one]

theorem ideleChar_ne_zero (a : Points F 1) : ideleChar F χ a ≠ 0 :=
  Units.ne_zero _

theorem continuous_ideleChar : Continuous (ideleChar F χ) :=
  Units.continuous_val.comp
    ((Automorphic.centralIdeleCharacter F χ).continuous.comp (continuous_ideleOf F))

theorem ideleChar_ideleRational (c : ideleRational F) : ideleChar F χ c = 1 := by
  obtain ⟨_, c', rfl⟩ := c
  have h : ideleOf F (AdelicGroupPoints.rational F (Scheme F 1) c') =
      diagonalUnits F (Matrix.GeneralLinearGroup.det
        (GeneralLinearGroupPoints.rationalEquiv F 1 c')) := by
    change AdelicGL.determinant F 1 (e 1 (AdelicGroupPoints.rational F (Scheme F 1) c')) = _
    rw [GeneralLinearGroupPoints.adelicHomeomorph_rational, determinant_rational]
  show (Automorphic.centralIdeleCharacter F χ
    (ideleOf F (AdelicGroupPoints.rational F (Scheme F 1) c')) : ℂ) = 1
  rw [h, Automorphic.centralIdeleCharacter_principal, Units.val_one]

theorem ideleChar_ideleRational_mul (c : ideleRational F) (a : Points F 1) :
    ideleChar F χ ((c : Points F 1) * a) = ideleChar F χ a := by
  rw [ideleChar_mul, ideleChar_ideleRational, one_mul]

theorem ideleChar_inv (z : Points F 1) : ideleChar F χ⁻¹ z = (ideleChar F χ z)⁻¹ := by
  simp only [ideleChar]
  rw [← Units.val_inv_eq_inv_val]
  rfl

theorem ideleChar_mul_char (χ' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (z : Points F 1) :
    ideleChar F (χ * χ') z = ideleChar F χ z * ideleChar F χ' z := by
  simp only [ideleChar]
  rw [← Units.val_mul]
  rfl

theorem detPower_one_eq (z : Points F 1) (w : ℂ) :
    detPower F 1 z w = Complex.exp (w * (logNorm F z : ℂ)) := rfl

/-- **Dichotomy for idele class characters.** Either `χ = |·|^w` for some `w`, or `χ` is
nontrivial on some idele of norm one. -/
theorem ideleChar_dichotomy :
    (∃ w : ℂ, ∀ z : Points F 1, ideleChar F χ z = detPower F 1 z w) ∨
      ∃ z₀ : Points F 1, detNorm F 1 z₀ = 1 ∧ ideleChar F χ z₀ ≠ 1 := by
  by_cases h : ∃ z₀ : Points F 1, detNorm F 1 z₀ = 1 ∧ ideleChar F χ z₀ ≠ 1
  · exact Or.inr h
  left
  have h' : ∀ z₀ : Points F 1, detNorm F 1 z₀ = 1 → ideleChar F χ z₀ = 1 := by
    intro z₀ hz₀
    by_contra hne
    exact h ⟨z₀, hz₀, hne⟩
  obtain ⟨w, hw⟩ := exists_eq_cexp_of_continuous (f := fun y => ideleChar F χ (normScale F y))
    ((continuous_ideleChar F χ).comp (continuous_normScale F))
    (by simp only [normScale_zero, ideleChar_one])
    (fun y y' => by simp only [normScale_add, ideleChar_mul])
  refine ⟨w, fun z => ?_⟩
  set y := logNorm F z with hy
  have hz : z = normScale F y * (normScale F (-y) * z) := by
    rw [← mul_assoc, ← normScale_add, add_neg_cancel, normScale_zero, one_mul]
  have h1 : detNorm F 1 (normScale F (-y) * z) = 1 := by
    rw [detNorm_one_mul, detNorm_normScale, Real.exp_neg, hy, logNorm,
      Real.exp_log (UnequalAnalytic.detNorm_pos F z)]
    exact inv_mul_cancel₀ (UnequalAnalytic.detNorm_pos F z).ne'
  have hval : ideleChar F χ z = Complex.exp (w * (y : ℂ)) := by
    conv_lhs => rw [hz]
    rw [ideleChar_mul, h' _ h1, mul_one]
    exact hw y
  rw [hval, detPower_one_eq]

/-- **Vanishing of character integrals.** If `χ(z₀) ≠ 1` for an idele `z₀` of norm one, then
`∫_(D₁) χ(a) u(log |a|) d^×a = 0` for every function `u`. -/
theorem integral_ideleChar_mul_eq_zero {z₀ : Points F 1} (hz₀ : detNorm F 1 z₀ = 1)
    (hχ : ideleChar F χ z₀ ≠ 1) (u : ℝ → ℂ) :
    ∫ a in ideleDomain F, ideleChar F χ a * u (logNorm F a) ∂ideleMeasure F = 0 := by
  set k : Points F 1 → ℂ := fun a => ideleChar F χ a * u (logNorm F a) with hkdef
  have hk : ∀ (c : ideleRational F) (x : Points F 1), k ((c : Points F 1) * x) = k x := by
    intro c x
    simp only [hkdef, ideleChar_ideleRational_mul, logNorm_ideleRational_mul]
  have h := setIntegral_comp_mul_left (ideleRational F) (ideleMeasure F)
    (isFundamentalDomain_ideleDomain F _) (measurableSet_ideleDomain F) z₀
    (points_one_mul_comm F z₀) k hk
  have hlog : ∀ a, logNorm F (z₀ * a) = logNorm F a := by
    intro a
    rw [logNorm, logNorm, detNorm_one_mul, hz₀, one_mul]
  have h2 : (fun x => k (z₀ * x)) = fun x => ideleChar F χ z₀ * k x := by
    funext x
    simp only [hkdef, ideleChar_mul, hlog, mul_assoc]
  rw [h2, integral_const_mul] at h
  have h3 : (ideleChar F χ z₀ - 1) * ∫ a in ideleDomain F, k a ∂ideleMeasure F = 0 := by
    rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hχ)

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
