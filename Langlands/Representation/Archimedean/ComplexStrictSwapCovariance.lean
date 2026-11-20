import Langlands.Representation.Archimedean.ComplexStrictSwapIntegral
import Langlands.Group.GL.UpperBruhatCells

/-! # Borel covariance of the ordinary complex adjacent-swap integral -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ} {i j : Fin n} (hj : (j : ℕ) = i + 1)

private abbrev rootElement (z : ℂ) : Langlands.GeneralLinear n ℂ :=
  Matrix.GeneralLinearGroup.transvection i j (ne_of_val_eq_succ hj) z

private theorem rootElement_mem (z : ℂ) :
    rootElement hj z ∈ upperUnipotent n ℂ := by
  have h := (chartUnipotent i j hj (-z)).2
  simpa only [chartUnipotent, neg_neg] using h

private theorem rootElement_mul_neg (z : ℂ) :
    rootElement hj (-z) * rootElement hj z = 1 := by
  apply Units.ext
  change Matrix.transvection i j (-z) * Matrix.transvection i j z = 1
  rw [Matrix.transvection_mul_transvection_same i j (ne_of_val_eq_succ hj)]
  simp

private theorem chart_mul_unipotent (u : upperUnipotent n ℂ) (z : ℂ) :
    ∃ v : upperUnipotent n ℂ,
      chart i j hj z * (u : Langlands.GeneralLinear n ℂ) =
        (v : Langlands.GeneralLinear n ℂ) * chart i j hj (z + u.val i j) := by
  let s : Langlands.GeneralLinear n ℂ := Matrix.GeneralLinearGroup.swap ℂ i j
  let t : ℂ := u.val i j
  let m := rootElement hj z * u.val * rootElement hj (-(z + t))
  have hm : m ∈ upperUnipotent n ℂ :=
    mul_mem (mul_mem (rootElement_mem hj z) u.2) (rootElement_mem hj (-(z + t)))
  have hmij : m i j = 0 := by
    change (Matrix.transvection i j z * u.val.val *
      Matrix.transvection i j (-(z + t))) i j = 0
    have huji : u.val j i = 0 := u.2.1 (lt_of_val_eq_succ hj)
    rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same, u.2.2 j, u.2.2 i, huji]
    change t + z * 1 + -(z + t) * (1 + z * 0) = 0
    ring
  have hconj : s * m * s ∈ upperUnipotent n ℂ := by
    rw [mem_upperUnipotent_iff]
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · change (Matrix.swap ℂ i j * m.val * Matrix.swap ℂ i j) a b = 0
      rw [swap_mul_mul_swap_apply]
      rcases swap_le_or hj hab.le with h | ⟨ha, hb⟩
      · exact hm.1 (lt_of_le_of_ne h fun he => hab.ne ((Equiv.swap i j).injective he))
      · rw [ha, hb]
        exact hmij
    · change (Matrix.swap ℂ i j * m.val * Matrix.swap ℂ i j) a a = 1
      rw [swap_mul_mul_swap_apply]
      exact hm.2 _
  have hsq : s * s = 1 := Units.ext (Matrix.swap_mul_self i j)
  refine ⟨⟨s * m * s, hconj⟩, ?_⟩
  change s * rootElement hj z * u.val =
    s * m * s * (s * rootElement hj (z + t))
  calc
    _ = s * (m * rootElement hj (z + t)) := by
      dsimp only [m]
      rw [mul_assoc (rootElement hj z * u.val), rootElement_mul_neg, mul_one, ← mul_assoc]
    _ = _ := by
      symm
      calc
        _ = (s * m) * (s * (s * rootElement hj (z + t))) := by rw [mul_assoc (s * m)]
        _ = (s * m) * rootElement hj (z + t) := by rw [← mul_assoc s s, hsq, one_mul]
        _ = _ := mul_assoc _ _ _

private theorem rootElement_mul_diagonal (a : Fin n → ℂˣ) (z : ℂ) :
    rootElement hj z * Iwasawa.diagonalUnits a =
      Iwasawa.diagonalUnits a * rootElement hj (((a j : ℂ) / (a i : ℂ)) * z) := by
  apply Units.ext
  change Matrix.transvection i j z * Matrix.diagonal (fun k => (a k : ℂ)) =
    Matrix.diagonal (fun k => (a k : ℂ)) *
      Matrix.transvection i j (((a j : ℂ) / (a i : ℂ)) * z)
  ext p q
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection, Matrix.add_apply]
  by_cases hpq : p = q
  · subst q
    have h : ¬(i = p ∧ j = p) := fun h => ne_of_val_eq_succ hj (h.1.trans h.2.symm)
    simp [h]
  · by_cases h : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.one_apply_ne hpq, Matrix.single_apply_same, zero_add]
      field_simp [(a i).ne_zero]
    · simp [Matrix.one_apply_ne hpq, h]

private theorem chart_mul_diagonal (a : Fin n → ℂˣ) (z : ℂ) :
    chart i j hj z * Iwasawa.diagonalUnits a =
      Iwasawa.diagonalUnits (fun k => a (Equiv.swap i j k)) *
        chart i j hj (((a j : ℂ) / (a i : ℂ)) * z) := by
  let s : Langlands.GeneralLinear n ℂ := permutation n ℂ (Equiv.swap i j)
  have hinv : (Equiv.swap i j)⁻¹ = Equiv.swap i j := Equiv.symm_swap i j
  have hs : s = Matrix.GeneralLinearGroup.swap ℂ i j := by
    apply Units.ext
    rw [permutation_coe, hinv]
    rfl
  have h : s * Iwasawa.diagonalUnits a =
      Iwasawa.diagonalUnits (fun k => a (Equiv.swap i j k)) * s := by
    simpa only [hinv] using permutation_mul_diagonalUnits n (Equiv.swap i j) a
  change Matrix.GeneralLinearGroup.swap ℂ i j * rootElement hj z * Iwasawa.diagonalUnits a =
    Iwasawa.diagonalUnits (fun k => a (Equiv.swap i j k)) *
      (Matrix.GeneralLinearGroup.swap ℂ i j * rootElement hj (((a j : ℂ) / (a i : ℂ)) * z))
  rw [← hs, mul_assoc, rootElement_mul_diagonal, ← mul_assoc, h, mul_assoc]

private theorem integral_comp_complex_mul (φ : ℂ → ℂ) {r : ℂ} (hr : r ≠ 0) :
    (∫ z, φ (r * z)) = (((‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z, φ z := by
  have hnorm : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hcoe : (‖r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm.ne'
  let u : Circle := ⟨r / (‖r‖ : ℂ),
    mem_sphere_zero_iff_norm.mpr (by simp [hnorm.ne'])⟩
  have hrotate (z : ℂ) : ‖r‖ • rotation u z = r * z := by
    rw [rotation_apply, Complex.real_smul]
    change (‖r‖ : ℂ) * (r / (‖r‖ : ℂ) * z) = r * z
    field_simp
  calc
    _ = ∫ z : ℂ, φ (‖r‖ • rotation u z) := by simp only [hrotate]
    _ = ∫ z : ℂ, φ (‖r‖ • z) :=
      MeasureTheory.integral_comp (rotation u) (fun z : ℂ => φ (‖r‖ • z))
    _ = _ := by
      rw [Measure.integral_comp_smul_of_nonneg volume φ ‖r‖ (hR := norm_nonneg r),
        Complex.finrank_real_complex, Complex.real_smul]

section Characters

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
  (hn : (pre ++ d :: e :: post).length = n) (hi : (i : ℕ) = pre.length)

local notation "ds" => (pre ++ d :: e :: post)
local notation "es" => (pre ++ e :: d :: post)

include hn hi hj in
private theorem principalSeriesCharacter_swap_jacobian (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds)
        (fun k => a (Equiv.swap i j k)) *
      (((‖(a j : ℂ) / (a i : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      principalSeriesCharacter ℂ n (complexPositionCharacter es) a := by
  let σ := Equiv.swap i j
  have hs : ComplexPermutation.swapPerm pre post d e hn = σ := by
    have h₁ : (⟨pre.length, by rw [← hn]; simp⟩ : Fin n) = i := Fin.ext hi.symm
    have h₂ : (⟨pre.length + 1, by rw [← hn]; simp⟩ : Fin n) = j := Fin.ext (by
      change pre.length + 1 = (j : ℕ)
      omega)
    rw [ComplexPermutation.swapPerm, h₁, h₂]
  have hσ (k : Fin n) : σ (σ k) = k := σ.left_inv k
  have hes : (es).length = n := (ComplexPermutation.length_swap pre post d e).trans hn
  have hχ (k : Fin n) (z : ℂˣ) :
      complexPositionCharacter ds k z = complexPositionCharacter es (σ k) z := by
    have hget := ComplexPermutation.get_swap pre post d e hn (σ k)
    rw [hs, Equiv.symm_apply_apply] at hget
    rw [ComplexPermutation.complexPositionCharacter_eq_get _ _ (hn.symm ▸ k.2),
      ComplexPermutation.complexPositionCharacter_eq_get _ _ (hes.symm ▸ (σ k).2)]
    exact congrArg (fun b : ComplexCharacterData => (b.character z : ℂ)) hget
  let x (k : Fin n) := ((‖(a k : ℂ)‖ ^ 2 : ℝ) : ℂ)
  let q (k : Fin n) := ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ)
  have hx (k : Fin n) : x k ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (a k).ne_zero))
  have hq : q i = q j + 1 := by
    dsimp only [q]
    rw [hj]
    push_cast
    ring
  have hschar :
      principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun k => a (σ k)) =
        ∏ k : Fin n, complexPositionCharacter es k (a k) * (x k) ^ (q (σ k)) := by
    unfold principalSeriesCharacter
    rw [Complex.finrank_real_complex]
    apply Fintype.prod_equiv σ
    intro k
    rw [hχ k, hσ k]
  let w (k : Fin n) : ℂ := if k = i then x i else if k = j then (x j)⁻¹ else 1
  have hij := ne_of_val_eq_succ hj
  have hw : (((‖(a j : ℂ) / (a i : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) = ∏ k : Fin n, w k := by
    rw [Fintype.prod_eq_mul i j hij (fun k hk => by simp [w, hk.1, hk.2])]
    rw [norm_div, div_pow, inv_div, Complex.ofReal_div, div_eq_mul_inv]
    simp [w, hij.symm, x]
  rw [hschar, hw, ← Finset.prod_mul_distrib, principalSeriesCharacter, Complex.finrank_real_complex]
  apply Finset.prod_congr rfl
  intro k _
  change complexPositionCharacter es k (a k) * (x k) ^ (q (σ k)) * w k =
    complexPositionCharacter es k (a k) * (x k) ^ (q k)
  rw [mul_assoc]
  congr 1
  by_cases hki : k = i
  · subst k
    rw [show w i = x i by simp [w], show σ i = j from Equiv.swap_apply_left i j]
    rw [hq, Complex.cpow_add _ _ (hx i), Complex.cpow_one]
  · by_cases hkj : k = j
    · subst k
      rw [show w j = (x j)⁻¹ by simp [w, hki], show σ j = i from Equiv.swap_apply_right i j]
      rw [hq, Complex.cpow_add _ _ (hx j), Complex.cpow_one, mul_assoc,
        mul_inv_cancel₀ (hx j), mul_one]
    · simp [σ, Equiv.swap_apply_of_ne_of_ne hki hkj, w, hki, hkj]

end Characters

/-- The chart integral applied to the right translate of a smooth vector. In the
strict convergence chamber it is absolutely convergent at each group element. -/
def strictSwapFunction (f : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  ∫ z, f (chart i j hj z * g)

theorem integrable_strictSwapFunction (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hi : (i : ℕ) = pre.length)
    (hre : 0 < (d.exponent - e.exponent).re)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ complexStandardModule n (pre ++ d :: e :: post)) (g : Langlands.GeneralLinear n ℂ) :
    Integrable fun z => f (chart i j hj z * g) :=
  integrable_chart_of_strict pre post d e i j hi hj hre
    (rightTranslation_mem_principalSeries _ hf g)

private theorem strictSwapFunction_unipotent {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)
    (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    strictSwapFunction hj f (u.val * g) = strictSwapFunction hj f g := by
  let φ (z : ℂ) := f (chart i j hj z * g)
  calc
    _ = ∫ z, φ (z + u.val i j) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      obtain ⟨v, hv⟩ := chart_mul_unipotent hj u z
      change f (chart i j hj z * (u.val * g)) = φ (z + u.val i j)
      rw [← mul_assoc, hv, mul_assoc]
      have he := hf.2 1 v (chart i j hj (z + u.val i j) * g)
      simpa only [map_one, one_mul, principalSeriesCharacter_one] using he
    _ = _ := integral_add_right_eq_self φ (u.val i j)

section Covariance

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
  (hn : (pre ++ d :: e :: post).length = n) (hi : (i : ℕ) = pre.length)

local notation "ds" => (pre ++ d :: e :: post)
local notation "es" => (pre ++ e :: d :: post)

include hn hi in
private theorem strictSwapFunction_diagonal {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ complexStandardModule n ds) (a : Fin n → ℂˣ) (g : Langlands.GeneralLinear n ℂ) :
    strictSwapFunction hj f (Iwasawa.diagonalUnits a * g) =
      principalSeriesCharacter ℂ n (complexPositionCharacter es) a * strictSwapFunction hj f g := by
  let φ (z : ℂ) := f (chart i j hj z * g)
  let r : ℂ := (a j : ℂ) / (a i : ℂ)
  let a' (k : Fin n) := a (Equiv.swap i j k)
  let c := principalSeriesCharacter ℂ n (complexPositionCharacter ds) a'
  have hr : r ≠ 0 := div_ne_zero (a j).ne_zero (a i).ne_zero
  calc
    _ = ∫ z, c * φ (r * z) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      change f (chart i j hj z * (Iwasawa.diagonalUnits a * g)) = c * φ (r * z)
      rw [← mul_assoc, chart_mul_diagonal, mul_assoc]
      have he := hf.2 a' 1 (chart i j hj (r * z) * g)
      simpa only [Subgroup.coe_one, mul_one] using he
    _ = c * ((((‖r‖ ^ 2)⁻¹ : ℝ) : ℂ) * strictSwapFunction hj f g) := by
      rw [integral_const_mul, integral_comp_complex_mul φ hr]
      rfl
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      exact principalSeriesCharacter_swap_jacobian hj pre post d e hn hi a

include hn hi in
/-- The nonzero strict swap intertwiner is given by the ordinary chart integral
at every element of `GL_n(ℂ)`. -/
theorem exists_strictSwapIntertwining_apply (hre : 0 < (d.exponent - e.exponent).re) :
    ∃ T : KFs n ds →ₗ[ℂ] KFs n es, T ≠ 0 ∧
      IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T ∧
      ∀ (g : Langlands.GeneralLinear n ℂ) (f : KFs n ds),
        (T f : Langlands.GeneralLinear n ℂ → ℂ) g = strictSwapFunction hj f.val g := by
  obtain ⟨T, hT₀, hT, hTK⟩ := exists_strictSwapIntertwining pre post d e hn i j hi hj hre
  refine ⟨T, hT₀, hT, fun g f => ?_⟩
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  have hf := mem_of_mem_kFs f.2
  have hTf := mem_of_mem_kFs (T f).2
  have hkval := hTK ⟨k, hk⟩ f
  rw [hTf.2, mul_assoc _ u.val k, strictSwapFunction_diagonal hj pre post d e hn hi hf,
    strictSwapFunction_unipotent hj hf]
  exact congrArg (fun v => principalSeriesCharacter ℂ n (complexPositionCharacter es) a * v) hkval

end Covariance

end Langlands.Archimedean.ComplexSwapJacquet
