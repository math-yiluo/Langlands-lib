import Langlands.Global.RankinSelberg.RealCompactDiracWeight

/-!
# The translated dual extension on the big cell

Let `a_t = diag(t^{n-1}, …, t, 1)` for `t ≥ 1`. For `κ ∈ O(n)` with nonzero corner minors
write `κ = b L` with `b` upper triangular and `L` lower unipotent. Then
`κ a_t⁻¹ = (b a_t⁻¹) Y` with `Y = a_t L a_t⁻¹` lower unipotent and `‖Y - 1‖ ≤ t⁻¹ ‖L - 1‖`.
For a sign-compatible continuous `ψ` and its dual extension `Ψ`, this gives

`φ₀(κ) Ψ(κ a_t⁻¹) = c_t W(κ) Ψ(Y)`,

with the scalar `c_t = ∏ₗ (t^{-(n-1-l)})^{s_l}` independent of `κ` and `W` the weight of
`RealCompactDiracWeight`.
-/

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear
open PrincipalSeriesExtension GramFormula RealPrincipalSeriesHilbert OrthogonalFinitePolynomial
open MatrixMinor LowerUnipotentRestriction

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## Inverses of determinant-one matrices -/

theorem norm_inv_le_of_det_eq_one (g : G) (hg : (g : Mat).det = 1) :
    ‖((g⁻¹ : G) : Mat)‖ ≤ n * (n.factorial * (1 + ‖(g : Mat)‖) ^ n) := by
  have hinv : ((g⁻¹ : G) : Mat) = (g : Mat).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hg, Ring.inverse_one, one_smul]
  rw [hinv]
  refine norm_le_of_abs_entry_le (by positivity) fun i j => ?_
  rw [Matrix.adjugate_apply]
  have hent : ∀ r c, |((g : Mat).updateRow j (Pi.single i 1)) r c| ≤ 1 + ‖(g : Mat)‖ := by
    intro r c
    rw [Matrix.updateRow_apply]
    split_ifs
    · by_cases hc : c = i
      · subst hc
        simp only [Pi.single_eq_same, abs_one]
        linarith [norm_nonneg (g : Mat)]
      · rw [Pi.single_eq_of_ne hc, abs_zero]
        positivity
    · linarith [abs_entry_le_norm (g : Mat) r c]
  have h := Matrix.det_le (A := (g : Mat).updateRow j (Pi.single i 1))
    (abv := AbsoluteValue.abs) hent
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

/-- A bound for the height base of a determinant-one matrix in terms of its norm. -/
theorem heightBase_le_of_det_eq_one (g : G) (hg : (g : Mat).det = 1) :
    heightBase g ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * n.factorial * (1 + ‖(g : Mat)‖) ^ (n + 1)) := by
  unfold heightBase
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hx : 0 ≤ ‖(g : Mat)‖ := norm_nonneg _
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hp1 : (1 : ℝ) ≤ (1 + ‖(g : Mat)‖) ^ n := one_le_pow₀ (by linarith)
  have hp : (1 + ‖(g : Mat)‖) ^ n ≤ (1 + ‖(g : Mat)‖) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
  have hp' : 1 + ‖(g : Mat)‖ ≤ (1 + ‖(g : Mat)‖) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbig : 1 + ‖(g : Mat)‖ ≤ ((n : ℝ) + 1) * n.factorial * (1 + ‖(g : Mat)‖) ^ (n + 1) := by
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) * n.factorial := by nlinarith
    nlinarith
  refine max_le (by linarith) (max_le (by linarith) ?_)
  calc ‖((g⁻¹ : G) : Mat)‖ ≤ n * (n.factorial * (1 + ‖(g : Mat)‖) ^ n) :=
        norm_inv_le_of_det_eq_one g hg
    _ ≤ ((n : ℝ) + 1) * n.factorial * (1 + ‖(g : Mat)‖) ^ (n + 1) := by
        have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
        calc (n : ℝ) * (n.factorial * (1 + ‖(g : Mat)‖) ^ n) ≤
            ((n : ℝ) + 1) * (n.factorial * (1 + ‖(g : Mat)‖) ^ (n + 1)) := by
              gcongr
          _ = _ := by ring

/-! ## The scaling torus -/

/-- The diagonal entries `max(t, 1)^{n-1-i}` of `a_t`. -/
def scaleUnits (n : ℕ) (t : ℝ) : Fin n → ℝˣ := fun i =>
  Units.mk0 (max t 1 ^ (n - 1 - (i : ℕ))) (pow_ne_zero _ (by positivity))

theorem scaleUnits_val (t : ℝ) (i : Fin n) :
    ((scaleUnits n t i : ℝˣ) : ℝ) = max t 1 ^ (n - 1 - (i : ℕ)) := rfl

theorem scaleUnits_pos (t : ℝ) (i : Fin n) : 0 < ((scaleUnits n t i : ℝˣ) : ℝ) := by
  rw [scaleUnits_val]
  positivity

/-- `τ_i / τ_j ≤ t⁻¹` for `j < i`, where `τ = scaleUnits n t`. -/
theorem scaleUnits_div_le {t : ℝ} (ht : 1 ≤ t) {i j : Fin n} (hji : j < i) :
    ((scaleUnits n t i : ℝˣ) : ℝ) * ((scaleUnits n t j : ℝˣ) : ℝ)⁻¹ ≤ t⁻¹ := by
  rw [scaleUnits_val, scaleUnits_val, max_eq_left ht]
  have hij : (j : ℕ) < i := hji
  have hexp : n - 1 - (j : ℕ) = (n - 1 - (i : ℕ)) + ((i : ℕ) - j) := by omega
  have ht0 : 0 < t := by linarith
  rw [hexp, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0.ne'), one_mul]
  have hk : 1 ≤ (i : ℕ) - j := by omega
  rw [inv_le_inv₀ (pow_pos ht0 _) ht0]
  calc t = t ^ 1 := (pow_one t).symm
    _ ≤ t ^ ((i : ℕ) - j) := pow_le_pow_right₀ ht hk

/-- The scalar `c_t = ∏ₗ (τₗ⁻¹)^{s_l}` with `τ = scaleUnits n t`. -/
def scaleFactor (s : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∏ l : Fin n, ((((scaleUnits n t l : ℝˣ) : ℝ)⁻¹ : ℝ) : ℂ) ^ s l

/-- Covariance of a function on `O(n)` under diagonal sign matrices by the inverse of the
sign character of `χ`, in the form used for extensions. -/
def IsSignCovariant (χ : ℕ → ℝˣ → ℂ) (ψ : O → ℂ) : Prop :=
  ∀ (d : Fin n → ℝˣ) (κ : O),
    ψ (signDiagonal (fun i => (d i : ℝ)) * κ) = (∏ i : Fin n, χ (i : ℕ) (signUnit (d i)))⁻¹ * ψ κ

theorem signReal_mul_of_pos {x y : ℝ} (hy : 0 < y) : signReal (x * y) = signReal x := by
  unfold signReal
  by_cases hx : 0 < x
  · rw [if_pos (mul_pos hx hy), if_pos hx]
  · rw [if_neg hx, if_neg]
    intro h
    exact hx (pos_of_mul_pos_left h hy.le)

theorem signReal_ne_zero (x : ℝ) : signReal x ≠ 0 := by
  unfold signReal
  split_ifs <;> norm_num

theorem pow_eq_signReal_mul_abs (x : ℝ) (k : ℕ) : x ^ k = signReal x ^ k * |x| ^ k := by
  rw [← mul_pow, RealTiedMinorProduct.signReal_mul_abs]

/-- **The big-cell decomposition of the translated dual extension.** -/
theorem bigCell_decomposition {χ : ℕ → ℝˣ → ℂ} {p : ℕ → ℕ} (hχ1 : ∀ l, χ l 1 = 1)
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (m : ℕ) (s : Fin n → ℂ) {ψ : O → ℂ}
    (hψ : IsSignCovariant χ ψ) (κ : O) (hQ : cornerProduct (κ : Mat) ≠ 0) {t : ℝ}
    (ht : 1 ≤ t) :
    ∃ Y : G, (Y : Mat).det = 1 ∧
      ‖(Y : Mat) - 1‖ ≤ t⁻¹ * (n * (lowerConstant n / |cornerProduct (κ : Mat)|)) ∧
      seedProfile p m κ *
          extension s ψ (Unitary.toUnits κ * (Iwasawa.diagonalUnits (scaleUnits n t) : G)⁻¹) =
        scaleFactor s t * weight p m s κ * extension s ψ Y := by
  set X : Mat := (κ : Mat) with hXdef
  have hQpos : 0 < |cornerProduct X| := abs_pos.2 hQ
  have hcn : ∀ l : ℕ, corner X l ≠ 0 := by
    intro l h
    have := abs_cornerProduct_le_corner κ l
    rw [← hXdef, h, abs_zero] at this
    linarith
  obtain ⟨b, L, hb, hL, hXe⟩ :=
    exists_upper_mul_lower_of_cornerNonzero n X (cornerNonzero_of_corner_ne_zero fun l _ => hcn l)
  have hβ : ∀ l : Fin n, corner X l = b l l * corner X ((l : ℕ) + 1) := fun l =>
    corner_eq_mul_succ hb hL hXe l.2
  have hbne : ∀ l : Fin n, b l l ≠ 0 := fun l h => hcn l (by rw [hβ l, h, zero_mul])
  have hβeq : ∀ l : Fin n, |b l l| = cornerRatio X l := by
    intro l
    rw [cornerRatio, hβ l, mul_div_cancel_right₀ _ (hcn _)]
  -- the scaling
  set τ : Fin n → ℝ := fun i => ((scaleUnits n t i : ℝˣ) : ℝ) with hτ
  have hτpos : ∀ i, 0 < τ i := fun i => scaleUnits_pos t i
  set Dinv : Mat := Matrix.diagonal fun i => (τ i)⁻¹ with hDinv
  set D : Mat := Matrix.diagonal τ with hD
  have hDD : Dinv * D = 1 := by
    rw [hDinv, hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hτpos i).ne'
  have hAinv : (((Iwasawa.diagonalUnits (scaleUnits n t) : G)⁻¹ : G) : Mat) = Dinv := by
    rw [← map_inv, Iwasawa.diagonalUnits_val, hDinv]
    congr 1
  -- the lower unipotent conjugate
  set Ym : Mat := D * L * Dinv with hYm
  have hYent : ∀ i j, Ym i j = τ i * L i j * (τ j)⁻¹ := by
    intro i j
    rw [hYm, hD, hDinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hYlow : IsLowerUnipotent Ym := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hYent, hL.1 i j hij, mul_zero, zero_mul]
    · rw [hYent, hL.2 i, mul_one, mul_inv_cancel₀ (hτpos i).ne']
  have hYdet : Ym.det = 1 := det_eq_one_of_isLowerUnipotent hYlow
  have hYunit : IsUnit Ym := by
    rw [Matrix.isUnit_iff_isUnit_det, hYdet]
    exact isUnit_one
  set Y : G := hYunit.unit with hYdef
  have hYval : (Y : Mat) = Ym := IsUnit.unit_spec hYunit
  refine ⟨Y, by rw [hYval, hYdet], ?_, ?_⟩
  · -- the distance to the identity
    rw [hYval]
    have hent : ∀ i j, |(Ym - 1) i j| ≤ t⁻¹ * |(L - 1) i j| := by
      intro i j
      rcases lt_trichotomy j i with hji | rfl | hij
      · have hne : i ≠ j := ne_of_gt hji
        rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, sub_zero,
          hYent, mul_comm (τ i), mul_assoc, abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [abs_of_pos (mul_pos (hτpos i) (inv_pos.2 (hτpos j)))]
        exact scaleUnits_div_le ht hji
      · rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_eq, hYlow.2 j, hL.2 j]
        simp
      · have hne : i ≠ j := ne_of_lt hij
        rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hne, hYlow.1 i j hij,
          hL.1 i j hij]
        simp
    have hL1 : ‖L - 1‖ ≤ n * (lowerConstant n / |cornerProduct X|) := by
      refine norm_le_of_abs_entry_le (by positivity [one_le_lowerConstant n]) fun i j => ?_
      rcases lt_trichotomy j i with hji | rfl | hij
      · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hji), sub_zero]
        have hX : X * Xᵀ = 1 := orthogonal_mul_transpose κ
        refine (abs_lower_entry_le hX hb hL hXe hji (hcn i)).trans ?_
        exact div_le_div_of_nonneg_left (by linarith [one_le_lowerConstant n]) hQpos
          (abs_cornerProduct_le_corner κ i)
      · rw [Matrix.sub_apply, Matrix.one_apply_eq, hL.2 j, sub_self, abs_zero]
        have : 0 ≤ lowerConstant n := by linarith [one_le_lowerConstant n]
        positivity
      · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), hL.1 i j hij, sub_zero,
          abs_zero]
        have : 0 ≤ lowerConstant n := by linarith [one_le_lowerConstant n]
        positivity
    have ht0 : 0 ≤ t⁻¹ := inv_nonneg.2 (by linarith)
    exact (norm_le_of_abs_entry_le_mul ht0 hent).trans (mul_le_mul_of_nonneg_left hL1 ht0)
  · -- the identity
    obtain ⟨a', u', k', hk', hYe⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact Y
    set bY : Mat := Matrix.diagonal (fun l => (a' l : ℝ)) * ((u' : G) : Mat) with hbYdef
    have hbY : bY.IsUpperTriangular := isUpperTriangular_diagonal_mul a' u'
    have hbYd : ∀ l, bY l l = a' l := diagonal_mul_apply_self a' u'
    have hbYne : ∀ l, bY l l ≠ 0 := fun l => by rw [hbYd]; exact (a' l).ne_zero
    have hYk : (Y : Mat) = bY * (k' : Mat) := by
      rw [hYe, hbYdef, Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
    set b' : Mat := b * Dinv with hb'def
    have hb' : b'.IsUpperTriangular := hb.mul (Matrix.blockTriangular_diagonal _)
    have hb'd : ∀ l, b' l l = b l l * (τ l)⁻¹ := fun l => by
      rw [hb'def, hDinv, Matrix.mul_diagonal]
    have hb'ne : ∀ l, b' l l ≠ 0 := fun l => by
      rw [hb'd]
      exact mul_ne_zero (hbne l) (inv_ne_zero (hτpos l).ne')
    set B : Mat := b' * bY with hBdef
    have hB : B.IsUpperTriangular := hb'.mul hbY
    have hBd : ∀ l, B l l = b' l l * bY l l := fun l => upperTriangular_mul_apply_self hb' hbY l
    have hBne : ∀ l, B l l ≠ 0 := fun l => by
      rw [hBd]
      exact mul_ne_zero (hb'ne l) (hbYne l)
    have hx : ((Unitary.toUnits κ * (Iwasawa.diagonalUnits (scaleUnits n t) : G)⁻¹ : G) : Mat) =
        B * (k' : Mat) := by
      rw [Units.val_mul, hAinv]
      change X * Dinv = _
      rw [hBdef, Matrix.mul_assoc, ← hYk, hYval, hYm, hXe, hb'def]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Dinv D, hDD, Matrix.one_mul]
    rw [extension_eq s ψ hB hBne hk' hx, extension_eq s ψ hbY hbYne hk' hYk]
    set d : Fin n → ℝˣ := fun i => Units.mk0 (b' i i) (hb'ne i) with hd
    have hsign : signDiagonal (fun i => B i i) =
        signDiagonal (fun i => (d i : ℝ)) * signDiagonal (fun i => bY i i) := by
      rw [← signDiagonal_mul (fun i => (d i).ne_zero) hbYne]
      congr 1
      funext i
      rw [hBd, hd, Units.val_mk0]
    rw [hsign, mul_assoc, hψ d]
    set Sg : ℝ := ∏ l : Fin n, signReal (b l l) ^ p l with hSg
    have hSgne : Sg ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun l _ => pow_ne_zero _ (signReal_ne_zero _)
    have hχprod : ∏ i : Fin n, χ (i : ℕ) (signUnit (d i)) = (Sg : ℂ) := by
      rw [hSg]
      push_cast
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [char_signUnit hχ1 hp, hd, Units.val_mk0, hb'd,
        signReal_mul_of_pos (inv_pos.2 (hτpos i))]
      push_cast
      rfl
    rw [hχprod]
    have hsgn : signPart p X = Sg * |signPart p X| := by
      rw [hSg, signPart, Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      have hs : signReal (corner X l * corner X ((l : ℕ) + 1)) = signReal (b l l) := by
        rw [hβ l, mul_assoc, signReal_mul_of_pos (mul_self_pos.2 (hcn _))]
      calc (corner X l * corner X ((l : ℕ) + 1)) ^ p l =
            (signReal (corner X l * corner X ((l : ℕ) + 1)) *
              |corner X l * corner X ((l : ℕ) + 1)|) ^ p l := by
            rw [RealTiedMinorProduct.signReal_mul_abs]
        _ = signReal (b l l) ^ p l * |(corner X l * corner X ((l : ℕ) + 1)) ^ p l| := by
            rw [mul_pow, abs_pow, hs]
    have habs : ∀ l : Fin n, ((|B l l| : ℝ) : ℂ) ^ s l =
        ((|b l l| : ℝ) : ℂ) ^ s l * ((((τ l)⁻¹ : ℝ) : ℂ) ^ s l * ((|bY l l| : ℝ) : ℂ) ^ s l) := by
      intro l
      rw [hBd, hb'd, abs_mul, abs_mul, abs_of_pos (inv_pos.2 (hτpos l)),
        Complex.ofReal_mul (|b l l| * (τ l)⁻¹) |bY l l|,
        Complex.mul_cpow_ofReal_nonneg (mul_nonneg (abs_nonneg _) (inv_pos.2 (hτpos l)).le)
          (abs_nonneg _), Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (inv_pos.2 (hτpos l)).le]
      ring
    have hratio : ratioProduct s X = ∏ l : Fin n, ((|b l l| : ℝ) : ℂ) ^ s l := by
      rw [ratioProduct]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [hβeq]
    have hsf : scaleFactor s t = ∏ l : Fin n, ((((τ l)⁻¹ : ℝ) : ℂ)) ^ s l := rfl
    have hsgnC : ((signPart p X : ℝ) : ℂ) = (Sg : ℂ) * ((|signPart p X| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← hsgn]
    simp only [habs, Finset.prod_mul_distrib]
    rw [seedProfile, seedReal, weight, ← hXdef, hratio, hsf, Complex.ofReal_mul,
      Complex.ofReal_mul, hsgnC]
    have hSgC : (Sg : ℂ) ≠ 0 := by exact_mod_cast hSgne
    field_simp

/-! ## The pointwise error -/

theorem norm_extension_sub_le (s : Fin n → ℂ) {Cκ Cω : ℝ} (hCω0 : 0 ≤ Cω)
    (hCκ : ∀ g : G, ‖((signedOrthogonalPart g : O) : Mat) - 1‖ ≤ Cκ * ‖(g : Mat) - 1‖)
    (hCω : ∀ g : G, ‖multiplier s g - 1‖ ≤
      Cω * ‖(g : Mat) - 1‖ * heightBase g ^ growthExponent s)
    (ψ : C(O, ℂ)) {L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ k l : O, ‖ψ k - ψ l‖ ≤ L * ‖(k : Mat) - (l : Mat)‖) (Y : G) :
    ‖extension s ψ Y - ψ 1‖ ≤
      Cω * ‖(Y : Mat) - 1‖ * heightBase Y ^ growthExponent s * ‖ψ‖ +
        L * (Cκ * ‖(Y : Mat) - 1‖) := by
  rw [extension_eq_multiplier]
  have h1 : multiplier s Y * ψ (signedOrthogonalPart Y) - ψ 1 =
      (multiplier s Y - 1) * ψ (signedOrthogonalPart Y) + (ψ (signedOrthogonalPart Y) - ψ 1) := by
    ring
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (hCω Y) (ψ.norm_coe_le_norm _) (norm_nonneg _) (by
      have := one_le_heightBase_rpow s Y
      have h0 : 0 ≤ ‖(Y : Mat) - 1‖ := norm_nonneg _
      positivity)
  · have h2 := hLip (signedOrthogonalPart Y) 1
    have h3 : ((1 : O) : Mat) = 1 := rfl
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (hCκ Y) hL0)


/-- The constant `(n+1)² n! (1 + n + n · lowerConstant n)^{n+1}` bounding the height base of
`Y` by a multiple of `|Q|^{-(n+1)}`. -/
def heightConstant (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (((n : ℝ) + 1) * n.factorial * (1 + n + n * lowerConstant n) ^ (n + 1))

theorem heightConstant_pos (n : ℕ) : 0 < heightConstant n := by
  unfold heightConstant
  have := one_le_lowerConstant n
  have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  positivity

/-- **The pointwise error on `O(n)`.** If `2m ≥ 1 + (n+2) q`, then
`‖φ₀(κ) Ψ(κ a_t⁻¹) - c_t W(κ) ψ(1)‖ ≤ ‖c_t‖ t⁻¹ (‖ψ‖ + L) K` for all `κ` and `t ≥ 1`. -/
theorem exists_pointwise_error {χ : ℕ → ℝˣ → ℂ} {p : ℕ → ℕ} (hχ1 : ∀ l, χ l 1 = 1)
    (hp : ∀ l, χ l (-1) = (-1) ^ p l) (s : Fin n → ℂ) {m : ℕ} (hm : 1 ≤ m)
    (hmq : 1 + ((n : ℝ) + 2) * growthExponent s ≤ 2 * m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψ : C(O, ℂ)) (L : ℝ), 0 ≤ L → IsSignCovariant χ ψ →
      (∀ k l : O, ‖ψ k - ψ l‖ ≤ L * ‖(k : Mat) - (l : Mat)‖) → ∀ (κ : O) {t : ℝ}, 1 ≤ t →
        ‖seedProfile p m κ *
            extension s ψ (Unitary.toUnits κ * (Iwasawa.diagonalUnits (scaleUnits n t) : G)⁻¹) -
          scaleFactor s t * weight p m s κ * ψ 1‖ ≤
            ‖scaleFactor s t‖ * (t⁻¹ * ((‖ψ‖ + L) * K)) := by
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_signedOrthogonalPart_sub_one_le (n := n)
  obtain ⟨Cω, hCω0, hCω⟩ := exists_norm_multiplier_sub_one_le s
  set q := growthExponent s with hq
  have hq0 : 0 ≤ q := growthExponent_nonneg s
  set lc := lowerConstant n with hlc
  have hlc1 : 1 ≤ lc := one_le_lowerConstant n
  set c₀ := heightConstant n with hc₀
  have hc₀pos : 0 < c₀ := heightConstant_pos n
  refine ⟨n * lc * (Cω * c₀ ^ q + Cκ), by positivity, fun ψ L hL0 hψ hLip κ t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have htinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hψn : 0 ≤ ‖ψ‖ := norm_nonneg _
  by_cases hQ : cornerProduct (κ : Mat) = 0
  · have h1 : seedProfile p m κ = 0 := by
      rw [seedProfile, seedReal, hQ, zero_pow (by omega), mul_zero, Complex.ofReal_zero]
    rw [h1, weight_of_cornerProduct_eq_zero p hm s κ hQ, zero_mul, mul_zero, zero_mul, sub_zero,
      norm_zero]
    positivity
  obtain ⟨Y, hdet, hY1, heq⟩ := bigCell_decomposition hχ1 hp m s hψ κ hQ ht
  rw [heq, ← mul_sub, norm_mul, norm_mul]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set Qa := |cornerProduct (κ : Mat)| with hQa
  have hQpos : 0 < Qa := abs_pos.2 hQ
  have hQ1 : Qa ≤ 1 := abs_cornerProduct_le_one κ
  set u := Qa⁻¹ with hu
  have hu1 : 1 ≤ u := one_le_inv₀ hQpos |>.2 hQ1
  have hupos : 0 < u := by linarith
  -- the distance of `Y` to the identity
  set y := ‖(Y : Mat) - 1‖ with hy
  have hy0 : 0 ≤ y := norm_nonneg _
  have hyB : y ≤ t⁻¹ * (n * lc * u) := by
    have : (n : ℝ) * (lc / Qa) = n * lc * u := by rw [hu, div_eq_mul_inv, mul_assoc]
    rw [← this]
    exact hY1
  have hyB' : y ≤ n * lc * u := hyB.trans (by
    have : 0 ≤ (n : ℝ) * lc * u := by positivity
    nlinarith)
  -- the height base of `Y`
  have hYnorm : ‖(Y : Mat)‖ ≤ n * lc * u + n := by
    calc ‖(Y : Mat)‖ = ‖((Y : Mat) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ y + ‖(1 : Mat)‖ := norm_add_le _ _
      _ ≤ n * lc * u + n := add_le_add hyB' norm_one_le
  have hhb : heightBase Y ≤ c₀ * u ^ (n + 1) := by
    refine (heightBase_le_of_det_eq_one Y hdet).trans ?_
    have hbase : 1 + ‖(Y : Mat)‖ ≤ (1 + n + n * lc) * u := by
      have : (1 : ℝ) + n ≤ (1 + n) * u := by nlinarith
      nlinarith
    have hpow : (1 + ‖(Y : Mat)‖) ^ (n + 1) ≤ ((1 + n + n * lc) * u) ^ (n + 1) :=
      pow_le_pow_left₀ (by positivity) hbase _
    rw [hc₀, heightConstant]
    have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc ((n : ℝ) + 1) * (((n : ℝ) + 1) * n.factorial * (1 + ‖(Y : Mat)‖) ^ (n + 1)) ≤
        ((n : ℝ) + 1) * (((n : ℝ) + 1) * n.factorial * ((1 + n + n * lc) * u) ^ (n + 1)) := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  have hhq : heightBase Y ^ q ≤ c₀ ^ q * u ^ (((n : ℝ) + 1) * q) := by
    calc heightBase Y ^ q ≤ (c₀ * u ^ (n + 1)) ^ q :=
          Real.rpow_le_rpow (by linarith [one_le_heightBase Y]) hhb hq0
      _ = c₀ ^ q * u ^ (((n : ℝ) + 1) * q) := by
          rw [Real.mul_rpow hc₀pos.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul
            hupos.le]
          push_cast
          ring_nf
  have hu' : 1 ≤ u ^ (((n : ℝ) + 1) * q) := Real.one_le_rpow hu1 (by positivity)
  -- the two factors
  have hd := norm_extension_sub_le s hCω0 hCκ hCω ψ hL0 hLip Y
  have ha := norm_weight_le p hm s κ
  rw [← hQa, ← hu] at ha
  have hE : Qa ^ (2 * m) * u ^ (1 + ((n : ℝ) + 2) * q) ≤ 1 := by
    rw [hu]
    exact pow_mul_inv_rpow_le_one hQpos hQ1 (by exact_mod_cast hmq)
  have hsplit : u ^ q * u * u ^ (((n : ℝ) + 1) * q) = u ^ (1 + ((n : ℝ) + 2) * q) := by
    have h1 : u ^ (1 + ((n : ℝ) + 2) * q) = u ^ q * u ^ (1 : ℝ) * u ^ (((n : ℝ) + 1) * q) := by
      rw [← Real.rpow_add hupos, ← Real.rpow_add hupos]
      congr 1
      ring
    rw [h1, Real.rpow_one]
  rw [← hq] at hd ha
  set W := ‖weight p m s κ‖ with hW
  set d := ‖extension s ψ Y - ψ 1‖ with hdd
  have hW0 : 0 ≤ W := norm_nonneg _
  have hcomb : Cω * c₀ ^ q * ‖ψ‖ + Cκ * L ≤ (Cω * c₀ ^ q + Cκ) * (‖ψ‖ + L) := by
    have : 0 ≤ Cω * c₀ ^ q := by positivity
    nlinarith
  have hd' : d ≤ y * u ^ (((n : ℝ) + 1) * q) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L) := by
    calc d ≤ Cω * y * heightBase Y ^ q * ‖ψ‖ + L * (Cκ * y) := hd
      _ ≤ Cω * y * (c₀ ^ q * u ^ (((n : ℝ) + 1) * q)) * ‖ψ‖ +
          L * (Cκ * y) * u ^ (((n : ℝ) + 1) * q) := by
          refine add_le_add ?_ (le_mul_of_one_le_right (by positivity) hu')
          gcongr
      _ = y * u ^ (((n : ℝ) + 1) * q) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L) := by ring
  calc W * d ≤ (Qa ^ (2 * m) * u ^ q) *
        (y * u ^ (((n : ℝ) + 1) * q) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L)) :=
        mul_le_mul ha hd' (norm_nonneg _) (by positivity)
    _ ≤ (Qa ^ (2 * m) * u ^ q) *
        (t⁻¹ * (n * lc * u) * u ^ (((n : ℝ) + 1) * q) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L)) := by
        gcongr
    _ = t⁻¹ * (n * lc) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L) *
        (Qa ^ (2 * m) * (u ^ q * u * u ^ (((n : ℝ) + 1) * q))) := by ring
    _ = t⁻¹ * (n * lc) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L) *
        (Qa ^ (2 * m) * u ^ (1 + ((n : ℝ) + 2) * q)) := by rw [hsplit]
    _ ≤ t⁻¹ * (n * lc) * (Cω * c₀ ^ q * ‖ψ‖ + Cκ * L) * 1 := by
        gcongr
    _ ≤ t⁻¹ * (n * lc) * ((Cω * c₀ ^ q + Cκ) * (‖ψ‖ + L)) := by
        rw [mul_one]
        gcongr
    _ = t⁻¹ * ((‖ψ‖ + L) * (n * lc * (Cω * c₀ ^ q + Cκ))) := by ring

end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
