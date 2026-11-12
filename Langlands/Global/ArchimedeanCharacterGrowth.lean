import Langlands.Global.ArchimedeanCharacterSmoothness
import Langlands.Global.ArchimedeanGrowth

/-! # Polynomial growth of the archimedean determinant factor of a Hecke character

Every continuous character `ψ` of the units of the mixed space is bounded by a constant times
a power of `max (1, ‖u‖, ‖u⁻¹‖)`. Write `u = s · exp a`, where `a` has the logarithms of the
absolute values at the real places and the principal logarithms at the complex places, and
`s² = 1`. Then `‖ψ s‖ = 1` and `ψ (exp a) = exp (L a)` for a continuous real-linear `L`. With
the Leibniz bound for the determinant, `g ↦ χ(det g)` has polynomial growth on the
archimedean matrix group for every Hecke character `χ`.
-/

noncomputable section

universe u

open scoped Classical Matrix.Norms.Operator
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

section MixedLog

variable {K : Type u} [Field K] [NumberField K]

theorem exp_mixedSpace_fst_apply (a : mixedSpace K) (v : {w : InfinitePlace K // IsReal w}) :
    (NormedSpace.exp a).1 v = Real.exp (a.1 v) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ)
    ((Pi.evalRingHom (fun _ => ℝ) v).comp (RingHom.fst _ _))
    ((continuous_apply v).comp continuous_fst) a
    ((NormedSpace.expSeries_radius_eq_top ℝ (mixedSpace K)).symm ▸ edist_lt_top _ _)

theorem exp_mixedSpace_snd_apply (a : mixedSpace K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (NormedSpace.exp a).2 w = Complex.exp (a.2 w) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ)
    ((Pi.evalRingHom (fun _ => ℂ) w).comp (RingHom.snd _ _))
    ((continuous_apply w).comp continuous_snd) a
    ((NormedSpace.expSeries_radius_eq_top ℝ (mixedSpace K)).symm ▸ edist_lt_top _ _)

omit [NumberField K] in
theorem units_fst_mul_inv (u : (mixedSpace K)ˣ) (v : {w : InfinitePlace K // IsReal w}) :
    (u : mixedSpace K).1 v * ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).1 v = 1 := by
  have h := congrArg (fun x : mixedSpace K => x.1 v) u.mul_inv
  simpa only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] using h

omit [NumberField K] in
theorem units_snd_mul_inv (u : (mixedSpace K)ˣ) (w : {w : InfinitePlace K // IsComplex w}) :
    (u : mixedSpace K).2 w * ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).2 w = 1 := by
  have h := congrArg (fun x : mixedSpace K => x.2 w) u.mul_inv
  simpa only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] using h

omit [NumberField K] in
theorem units_fst_ne_zero (u : (mixedSpace K)ˣ) (v : {w : InfinitePlace K // IsReal w}) :
    (u : mixedSpace K).1 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (units_fst_mul_inv u v)

omit [NumberField K] in
theorem units_snd_ne_zero (u : (mixedSpace K)ˣ) (w : {w : InfinitePlace K // IsComplex w}) :
    (u : mixedSpace K).2 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (units_snd_mul_inv u w)

/-- The logarithm of a unit of the mixed space: the logarithms of the absolute values at the
real places and the principal logarithms at the complex places. -/
def mixedLog (u : (mixedSpace K)ˣ) : mixedSpace K :=
  (fun v => Real.log |(u : mixedSpace K).1 v|, fun w => Complex.log ((u : mixedSpace K).2 w))

/-- The sign part `u · exp (-mixedLog u)` of a unit squares to one. -/
theorem sign_mul_sign_eq_one (u : (mixedSpace K)ˣ) :
    (u * (banachExpUnit (mixedLog u))⁻¹) * (u * (banachExpUnit (mixedLog u))⁻¹) = 1 := by
  apply Units.ext
  change ((u : mixedSpace K) * NormedSpace.exp (-mixedLog u)) *
      ((u : mixedSpace K) * NormedSpace.exp (-mixedLog u)) = 1
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply,
      exp_mixedSpace_fst_apply, Prod.fst_neg, Pi.neg_apply, mixedLog, Real.exp_neg,
      Real.exp_log (abs_pos.mpr (units_fst_ne_zero u v))]
    have h := units_fst_ne_zero u v
    have habs : |(u : mixedSpace K).1 v| ≠ 0 := abs_ne_zero.mpr h
    calc
      _ = ((u : mixedSpace K).1 v * (u : mixedSpace K).1 v) *
          (|(u : mixedSpace K).1 v| * |(u : mixedSpace K).1 v|)⁻¹ := by
        rw [mul_inv]
        ring
      _ = 1 := by
        rw [← abs_mul_abs_self ((u : mixedSpace K).1 v), mul_inv_cancel₀ (mul_ne_zero habs habs)]
  · simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply,
      exp_mixedSpace_snd_apply, Prod.snd_neg, Pi.neg_apply, mixedLog, Complex.exp_neg,
      Complex.exp_log (units_snd_ne_zero u w)]
    rw [mul_inv_cancel₀ (units_snd_ne_zero u w), one_mul]

theorem abs_log_le_log_of_le {y M : ℝ} (hy : 0 < y) (h1 : y ≤ M) (h2 : y⁻¹ ≤ M) :
    |Real.log y| ≤ Real.log M := by
  rw [abs_le]
  constructor
  · rw [neg_le, ← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hy) h2
  · exact Real.log_le_log hy h1

/-- The height of a unit: the maximum of one, its norm and the norm of its inverse. -/
def unitHeight (u : (mixedSpace K)ˣ) : ℝ :=
  max 1 (max ‖(u : mixedSpace K)‖ ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)‖)

theorem one_le_unitHeight (u : (mixedSpace K)ˣ) : 1 ≤ unitHeight u := le_max_left _ _

theorem norm_le_unitHeight (u : (mixedSpace K)ˣ) : ‖(u : mixedSpace K)‖ ≤ unitHeight u :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_inv_le_unitHeight (u : (mixedSpace K)ˣ) :
    ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)‖ ≤ unitHeight u :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem norm_mixedLog_le (u : (mixedSpace K)ˣ) :
    ‖mixedLog u‖ ≤ Real.log (unitHeight u) + Real.pi := by
  have hM := one_le_unitHeight u
  have hlog : 0 ≤ Real.log (unitHeight u) := Real.log_nonneg hM
  have hb : 0 ≤ Real.log (unitHeight u) + Real.pi := add_nonneg hlog Real.pi_pos.le
  have hfst : ∀ v, ‖(u : mixedSpace K).1 v‖ ≤ unitHeight u := fun v =>
    ((norm_le_pi_norm _ v).trans (norm_fst_le _)).trans (norm_le_unitHeight u)
  have hfst' : ∀ v, ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).1 v‖ ≤ unitHeight u := fun v =>
    ((norm_le_pi_norm _ v).trans (norm_fst_le _)).trans (norm_inv_le_unitHeight u)
  have hsnd : ∀ w, ‖(u : mixedSpace K).2 w‖ ≤ unitHeight u := fun w =>
    ((norm_le_pi_norm _ w).trans (norm_snd_le _)).trans (norm_le_unitHeight u)
  have hsnd' : ∀ w, ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).2 w‖ ≤ unitHeight u := fun w =>
    ((norm_le_pi_norm _ w).trans (norm_snd_le _)).trans (norm_inv_le_unitHeight u)
  refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg hb).mpr fun v => ?_,
    (pi_norm_le_iff_of_nonneg hb).mpr fun w => ?_⟩
  · change ‖Real.log |(u : mixedSpace K).1 v|‖ ≤ _
    rw [Real.norm_eq_abs]
    have hinv : |(u : mixedSpace K).1 v|⁻¹ =
        ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).1 v‖ := by
      rw [Real.norm_eq_abs, ← abs_inv, inv_eq_of_mul_eq_one_right (units_fst_mul_inv u v)]
    have h := abs_log_le_log_of_le (abs_pos.mpr (units_fst_ne_zero u v))
      (by simpa only [Real.norm_eq_abs] using hfst v) (hinv ▸ hfst' v)
    linarith [Real.pi_pos]
  · change ‖Complex.log ((u : mixedSpace K).2 w)‖ ≤ _
    have hinv : ‖(u : mixedSpace K).2 w‖⁻¹ =
        ‖((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K).2 w‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right (units_snd_mul_inv u w)]
    have h := abs_log_le_log_of_le (norm_pos_iff.mpr (units_snd_ne_zero u w))
      (hsnd w) (hinv ▸ hsnd' w)
    calc
      _ ≤ |(Complex.log ((u : mixedSpace K).2 w)).re| +
          |(Complex.log ((u : mixedSpace K).2 w)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Real.log (unitHeight u) + Real.pi := by
        rw [Complex.log_re, Complex.log_im]
        exact add_le_add h (Complex.abs_arg_le_pi _)

/-- A continuous character of the units of the mixed space has polynomial growth in the
height of a unit. -/
theorem exists_norm_unitsCharacter_le (ψ : (mixedSpace K)ˣ →ₜ* ℂˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ u : (mixedSpace K)ˣ,
      ‖(ψ u : ℂ)‖ ≤ C * unitHeight u ^ d := by
  obtain ⟨L, hL⟩ := exists_unitsCharacter_exp ψ
  refine ⟨Real.exp (‖L‖ * Real.pi), (Real.exp_pos _).le, ⌈‖L‖⌉₊, fun u => ?_⟩
  set s := u * (banachExpUnit (mixedLog u))⁻¹ with hs
  have hu : u = s * banachExpUnit (mixedLog u) := by rw [hs, inv_mul_cancel_right]
  have hψs : ‖(ψ s : ℂ)‖ = 1 := by
    have h2 : (ψ s : ℂ) * ψ s = 1 := by
      rw [← Units.val_mul, ← map_mul, sign_mul_sign_eq_one, map_one, Units.val_one]
    have h3 : ‖(ψ s : ℂ)‖ * ‖(ψ s : ℂ)‖ = 1 := by rw [← norm_mul, h2, norm_one]
    nlinarith [norm_nonneg (ψ s : ℂ)]
  have hM := one_le_unitHeight u
  have hlog : 0 ≤ Real.log (unitHeight u) := Real.log_nonneg hM
  calc
    ‖(ψ u : ℂ)‖ = ‖Complex.exp (L (mixedLog u))‖ := by
      have hsplit : (ψ u : ℂ) = ψ s * ψ (banachExpUnit (mixedLog u)) := by
        rw [← Units.val_mul, ← map_mul, ← hu]
      rw [hsplit, norm_mul, hψs, one_mul, hL]
    _ = Real.exp (L (mixedLog u)).re := Complex.norm_exp _
    _ ≤ Real.exp (‖L‖ * (Real.log (unitHeight u) + Real.pi)) := by
      apply Real.exp_le_exp.mpr
      calc
        (L (mixedLog u)).re ≤ ‖L (mixedLog u)‖ := Complex.re_le_norm _
        _ ≤ ‖L‖ * ‖mixedLog u‖ := L.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_mixedLog_le u) (norm_nonneg _)
    _ = Real.exp (‖L‖ * Real.pi) * Real.exp (‖L‖ * Real.log (unitHeight u)) := by
      rw [← Real.exp_add]
      ring_nf
    _ ≤ Real.exp (‖L‖ * Real.pi) * Real.exp ((⌈‖L‖⌉₊ : ℝ) * Real.log (unitHeight u)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog)
    _ = Real.exp (‖L‖ * Real.pi) * unitHeight u ^ ⌈‖L‖⌉₊ := by
      rw [Real.exp_nat_mul, Real.exp_log (lt_of_lt_of_le zero_lt_one hM)]

end MixedLog

section Determinant

variable {R : Type*} [NormedCommRing R]

/-- The Leibniz bound for the determinant over a normed commutative ring. -/
theorem norm_det_le_factorial_mul_pow {m : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin m) R)
    (B : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ (m.factorial : ℝ) * B ^ m := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ s : Equiv.Perm (Fin m), ‖Equiv.Perm.sign s • ∏ i, A (s i) i‖ := norm_sum_le _ _
    _ = ∑ s : Equiv.Perm (Fin m), ‖∏ i, A (s i) i‖ := by simp only [norm_units_zsmul]
    _ ≤ ∑ _s : Equiv.Perm (Fin m), B ^ m := by
      apply Finset.sum_le_sum
      intro s _
      calc
        ‖∏ i, A (s i) i‖ ≤ ∏ i, ‖A (s i) i‖ := Finset.norm_prod_le' _ hne _
        _ ≤ ∏ _i : Fin m, B := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => hA (s i) i)
        _ = B ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]

end Determinant

namespace ArchimedeanGL

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

theorem norm_entry_le (A : ArchimedeanMatrix K n) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ k, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ k, ‖A i k‖₊ ≤ (Finset.univ : Finset (Fin n)).sup fun l => ∑ k, ‖A l k‖₊ :=
    Finset.le_sup (f := fun l => ∑ k, ‖A l k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

theorem norm_det_le (hn : 0 < n) (A : ArchimedeanMatrix K n) :
    ‖A.det‖ ≤ (n.factorial : ℝ) * ‖A‖ ^ n :=
  norm_det_le_factorial_mul_pow hn A ‖A‖ (norm_entry_le A)

/-- The height of the determinant is bounded by a power of the matrix height. -/
theorem unitHeight_det_le (hn : 0 < n) (x : InfiniteAdelicGL K n) :
    unitHeight (Matrix.GeneralLinearGroup.det (archimedeanGLCoordinates K n x)) ≤
      (n.factorial : ℝ) * matrixHeight K n x ^ n := by
  set y := archimedeanGLCoordinates K n x
  have hH := one_le_matrixHeight K n x
  have hf : (1 : ℝ) ≤ n.factorial := Nat.one_le_cast.mpr (Nat.factorial_pos n)
  have hpow : (1 : ℝ) ≤ matrixHeight K n x ^ n := one_le_pow₀ hH
  have hfac : 0 ≤ (n.factorial : ℝ) := by positivity
  apply max_le (one_le_mul_of_one_le_of_one_le hf hpow)
  apply max_le
  · calc
      ‖((Matrix.GeneralLinearGroup.det y : (mixedSpace K)ˣ) : mixedSpace K)‖ =
          ‖(y.val : ArchimedeanMatrix K n).det‖ := rfl
      _ ≤ (n.factorial : ℝ) * ‖y.val‖ ^ n := norm_det_le hn _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_val_le_matrixHeight K n x) n) hfac
  · calc
      ‖(((Matrix.GeneralLinearGroup.det y)⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)‖ =
          ‖(y.inv : ArchimedeanMatrix K n).det‖ := by
        rw [← map_inv]
        rfl
      _ ≤ (n.factorial : ℝ) * ‖y.inv‖ ^ n := norm_det_le hn _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_inv_le_matrixHeight K n x) n) hfac

/-- Multiplying by a function of polynomial growth keeps polynomial growth. -/
theorem HasPolynomialGrowth.mul {f h : InfiniteAdelicGL K n → ℂ}
    (hf : HasPolynomialGrowth K n f) (hh : HasPolynomialGrowth K n h) :
    HasPolynomialGrowth K n (fun g => f g * h g) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hh⟩ := hh
  refine ⟨C * D, mul_nonneg hC hD, d + e, fun g => ?_⟩
  calc
    ‖f g * h g‖ = ‖f g‖ * ‖h g‖ := norm_mul _ _
    _ ≤ (C * matrixHeight K n g ^ d) * (D * matrixHeight K n g ^ e) :=
      mul_le_mul (hf g) (hh g) (norm_nonneg _)
        (mul_nonneg hC (pow_nonneg (matrixHeight_nonneg K n g) d))
    _ = C * D * matrixHeight K n g ^ (d + e) := by rw [pow_add]; ring

end ArchimedeanGL

namespace HeckeCharacter

variable {K : Type u} [Field K] [NumberField K]

/-- The archimedean determinant factor of every Hecke character has polynomial growth. -/
theorem hasPolynomialGrowth_adelicDeterminant_ofInfinite (χ : HeckeCharacter K) (n : ℕ) :
    ArchimedeanGL.HasPolynomialGrowth K n
      (fun g => (χ.adelicDeterminant n (AdelicGL.ofInfinite K n g) : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_le_one, 0, fun g => ?_⟩
    have hdet : AdelicGL.determinant K 0 (AdelicGL.ofInfinite K 0 g) = 1 := by
      apply Units.ext
      exact Matrix.det_isEmpty
    change ‖(χ.onIdeles (AdelicGL.determinant K 0 (AdelicGL.ofInfinite K 0 g)) : ℂ)‖ ≤ _
    rw [hdet, map_one, Units.val_one, norm_one, pow_zero, mul_one]
  obtain ⟨C, hC, d, hψ⟩ := exists_norm_unitsCharacter_le χ.mixedCharacter
  refine ⟨C * (n.factorial : ℝ) ^ d, by positivity, n * d, fun g => ?_⟩
  have hg : g = (archimedeanGLCoordinates K n).symm (archimedeanGLCoordinates K n g) :=
    ((archimedeanGLCoordinates K n).symm_apply_apply g).symm
  have hval : χ.adelicDeterminant n (AdelicGL.ofInfinite K n g) =
      χ.mixedCharacter (Matrix.GeneralLinearGroup.det (archimedeanGLCoordinates K n g)) := by
    conv_lhs => rw [hg]
    exact χ.adelicDeterminant_ofInfinite_coordinates n _
  show ‖(χ.adelicDeterminant n (AdelicGL.ofInfinite K n g) : ℂ)‖ ≤ _
  rw [hval]
  calc
    _ ≤ C * unitHeight (Matrix.GeneralLinearGroup.det (archimedeanGLCoordinates K n g)) ^ d :=
      hψ _
    _ ≤ C * ((n.factorial : ℝ) * ArchimedeanGL.matrixHeight K n g ^ n) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (le_trans zero_le_one (one_le_unitHeight _))
        (ArchimedeanGL.unitHeight_det_le hn g) d) hC
    _ = C * (n.factorial : ℝ) ^ d * ArchimedeanGL.matrixHeight K n g ^ (n * d) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

end HeckeCharacter

end Langlands.Global
