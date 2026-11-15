import Langlands.Representation.Archimedean.ComplexSwapJacquetChart
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof

/-!
# Right derivatives of principal-series functions along the rank-one chart

Let `f` lie in the smooth principal series `complexStandardModule n ds` of `GL_n(ℂ)`, let
`i` and `j = i + 1` be adjacent positions, and let `C(z) = chart i j hj z = s x(z)` be the
permutation matrix `s` of the transposition `(i j)` times `x(z) = 1 + z E_{ij}`. Write
`R(X)` for the right derivative and `φ(z) = f(C(z))`. This file computes `R(X) f` at the points
`C(z)` and at the identity, for every direction needed by the rank-one Jacquet functional:

* `contDiff_chartRestrict`: `φ` is smooth on `ℂ` (as a real manifold);
* `rightDerivative_chart_single_ij`: `R(w E_{ij}) f (C(z)) = Dφ(z)(w)`;
* `rightDerivative_chart_strictUpper`: `R(X) f (C(z)) = 0` for `X` strictly upper triangular with
  `X_{ij} = 0`;
* `rightDerivative_chart_diag_other`: `R(c E_{kk}) f (C(z)) = κ_k(c) f(C(z))` for `k ≠ i, j`;
* `rightDerivative_chart_diag_j`: `R(c E_{jj}) f (C(z)) = κ_i(c) f(C(z)) + Dφ(z)(c z)`;
* `rightDerivative_chart_diag_i`: `R(c E_{ii}) f (C(z)) = κ_j(c) f(C(z)) - Dφ(z)(c z)`;
* `rightDerivative_one_strictUpper`, `rightDerivative_one_diag`: at the identity, `R(X) f (1) = 0`
  for strictly upper triangular `X` and `R(c E_{kk}) f (1) = κ_k(c) f(1)`.

Here `κ_k(c) = kappa ds hn k c = Re c · (2 t_k + (n - 1) - 2k) + Im c · i l_k`.

The proofs work in matrix coordinates (`rightDerivative_eq_fderiv`): `R(X) f (g)` is the
derivative of the extension `f̃ = unitsExtension f` at `g` in the direction `g X`. Two
equivariance facts of `f̃` do all the work: `f̃(u y) = f̃(y)` for upper unipotent `u`, which kills
the directions `N y` with `N` strictly upper triangular
(`ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero`), and
`f̃(diag(a) y) = χδ^{1/2}(a) f̃(y)`, which gives `Df̃(y)(c E_{kk} y) = κ_k(c) f̃(y)`
(`fderiv_unitsExtension_single_mul`, by differentiating along `t ↦ diag(1, …, e^{tc}, …, 1) y`).
The remaining input is the matrix algebra of `C(z)`:
`C(z) E_{ij} = s E_{ij} = E_{jj}`, `C(z) (c E_{jj}) = (c E_{ii}) C(z) + C(z) (c z E_{ij})`,
`C(z) (c E_{ii}) = (c E_{jj}) C(z) - C(z) (c z E_{ij})`, `E_{kk}` commutes with `C(z)` for
`k ≠ i, j`, and `C(z) X C(z)⁻¹ = s (x(z) X x(-z)) s` is strictly upper triangular when `X` is
strictly upper triangular with `X_{ij} = 0`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-! ## Characters -/

theorem unitChar_one (μ : ℤ) (w : ℂ) : unitChar μ w 1 = 1 := by
  simp [unitChar]

/-- The principal-series character is trivial at the identity. -/
theorem principalSeriesCharacter_one (ds : List ComplexCharacterData) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) 1 = 1 := by
  rw [principalSeriesCharacter_eq]
  exact Finset.prod_eq_one fun i _ => by rw [Pi.one_apply, Units.val_one, unitChar_one]

/-- `z ↦ (z/|z|)^μ |z|^(2w)` at `z = e^x`. -/
theorem unitChar_exp (μ : ℤ) (w x : ℂ) :
    unitChar μ w (Complex.exp x) =
      Complex.exp ((μ : ℂ) * (Complex.I * (x.im : ℂ)) + 2 * w * (x.re : ℂ)) := by
  have hdiv : Complex.exp x / ((‖Complex.exp x‖ : ℝ) : ℂ) =
      Complex.exp (Complex.I * (x.im : ℂ)) := by
    rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub]
    congr 1
    linear_combination (-1 : ℂ) * Complex.re_add_im x
  rw [unitChar, hdiv, ← Complex.exp_int_mul, Complex.norm_exp, Real.log_exp, ← Complex.exp_add]

theorem posWeight_eq_get : ∀ (l : List ComplexCharacterData) (p : ℕ) (hp : p < l.length),
    posWeight l p = (l.get ⟨p, hp⟩).weight
  | [], p, hp => absurd hp (Nat.not_lt_zero p)
  | _ :: _, 0, _ => rfl
  | _ :: l, p + 1, hp => posWeight_eq_get l p (Nat.lt_of_succ_lt_succ hp)

theorem posExponent_eq_get : ∀ (l : List ComplexCharacterData) (p : ℕ) (hp : p < l.length),
    posExponent l p = (l.get ⟨p, hp⟩).exponent
  | [], p, hp => absurd hp (Nat.not_lt_zero p)
  | _ :: _, 0, _ => rfl
  | _ :: l, p + 1, hp => posExponent_eq_get l p (Nat.lt_of_succ_lt_succ hp)

/-- `κ_k(c)` in terms of the weight and exponent of the position `k`. -/
theorem kappa_eq (ds : List ComplexCharacterData) (hn : ds.length = n) (k : Fin n) (c : ℂ) :
    kappa ds hn k c = (posWeight ds k : ℂ) * (Complex.I * (c.im : ℂ)) +
      2 * (posExponent ds k + (((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))) * (c.re : ℂ) := by
  have hw : posWeight ds k = (ds.get (Fin.cast hn.symm k)).weight :=
    posWeight_eq_get ds k (hn.symm ▸ k.2)
  have he : posExponent ds k = (ds.get (Fin.cast hn.symm k)).exponent :=
    posExponent_eq_get ds k (hn.symm ▸ k.2)
  rw [kappa, hw, he]
  ring

/-! ## Equivariance of the extension to matrices -/

/-- The extension `f̃` of a principal-series function is invariant under left multiplication by
upper unipotent matrices. -/
theorem unitsExtension_unipotent_mul_eq {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)
    (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    unitsExtension f (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        (g : Matrix (Fin n) (Fin n) ℂ)) =
      unitsExtension f (g : Matrix (Fin n) (Fin n) ℂ) := by
  rw [ComplexDuality.LieInvariance.unitsExtension_unipotent_mul hf u g,
    principalSeriesCharacter_one, one_mul, unitsExtension_val]

/-- The derivative of `f̃` at `g` along `c E_kk g` is `κ_k(c) f(g)`. -/
theorem fderiv_unitsExtension_single_mul {ds : List ComplexCharacterData} (hn : ds.length = n)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds) (k : Fin n)
    (c : ℂ) (g : Langlands.GeneralLinear n ℂ) :
    fderiv ℝ (unitsExtension f) (g : Matrix (Fin n) (Fin n) ℂ)
        (Matrix.single k k c * (g : Matrix (Fin n) (Fin n) ℂ)) = kappa ds hn k c * f g := by
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = (posWeight ds k : ℂ) * (Complex.I * (c.im : ℂ)) +
      2 * (posExponent ds k + (((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))) * (c.re : ℂ) := ⟨_, rfl⟩
  let a : ℝ → Fin n → ℂˣ := fun t l =>
    if l = k then Units.mk0 (Complex.exp ((t : ℂ) * c)) (Complex.exp_ne_zero _) else 1
  let γ : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t =>
    (g : Matrix (Fin n) (Fin n) ℂ) + (Complex.exp ((t : ℂ) * c) - 1) •
      (Matrix.single k k (1 : ℂ) * (g : Matrix (Fin n) (Fin n) ℂ))
  have hdiag : ∀ t : ℝ, Matrix.diagonal (fun l => (a t l : ℂ)) =
      1 + (Complex.exp ((t : ℂ) * c) - 1) • Matrix.single k k (1 : ℂ) := by
    intro t
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p = k
      · subst hp
        simp [a]
      · simp [a, hp, Ne.symm hp]
    · have hkpq : ¬(k = p ∧ k = q) := fun h => hpq (h.1.symm.trans h.2)
      simp [Matrix.diagonal_apply_ne _ hpq, Matrix.one_apply_ne hpq, hkpq]
  have hγeq : ∀ t : ℝ,
      γ t = Matrix.diagonal (fun l => (a t l : ℂ)) * (g : Matrix (Fin n) (Fin n) ℂ) := by
    intro t
    rw [hdiag t, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hγ : HasDerivAt γ (Matrix.single k k c * (g : Matrix (Fin n) (Fin n) ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) - 1) c 0 := by
      have h := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c).cexp).sub_const 1
      simpa using h
    have h2 := (h1.smul_const
      (Matrix.single k k (1 : ℂ) * (g : Matrix (Fin n) (Fin n) ℂ))).const_add
        (g : Matrix (Fin n) (Fin n) ℂ)
    have h3 : c • (Matrix.single k k (1 : ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.single k k c * (g : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← Matrix.smul_mul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h3] at h2
    exact h2
  have hγ0 : (g : Matrix (Fin n) (Fin n) ℂ) = γ 0 := by simp [γ]
  have hcomp := (differentiableAt_unitsExtension hf.1 (Units.isUnit g)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hγ hγ0
  have hfun : (unitsExtension f ∘ γ) = fun t : ℝ => Complex.exp ((t : ℂ) * K) * f g := by
    funext t
    rw [Function.comp_apply, hγeq t,
      ComplexDuality.LieInvariance.unitsExtension_diagonal_mul hf (a t) g,
      principalSeriesCharacter_eq, Finset.prod_eq_single k]
    · congr 1
      simp only [a, ↓reduceIte, Units.val_mk0]
      rw [unitChar_exp, hK]
      congr 1
      simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      push_cast
      ring
    · intro l _ hl
      simp only [a, hl, ↓reduceIte, Units.val_one, unitChar_one]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [hfun] at hcomp
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K) * f g) (K * f g) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const K).cexp).mul_const (f g)
    simpa using h
  rw [hcomp.unique hd, kappa_eq, ← hK]

/-! ## Matrix algebra of the chart -/

section Algebra

variable {i j : Fin n}

theorem swap_mul_single (i j a b : Fin n) (x : ℂ) :
    Matrix.swap ℂ i j * Matrix.single a b x = Matrix.single (Equiv.swap i j a) b x := by
  rw [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul]
  ext p q
  simp only [Matrix.submatrix_apply, id, Matrix.single_apply, Equiv.swap_apply_eq_iff]

theorem single_mul_swap (i j a b : Fin n) (x : ℂ) :
    Matrix.single a b x * Matrix.swap ℂ i j = Matrix.single a (Equiv.swap i j b) x := by
  rw [Matrix.swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap]
  ext p q
  simp only [Matrix.submatrix_apply, id, Matrix.single_apply, Equiv.swap_apply_eq_iff]

theorem swap_mul_mul_swap_apply (i j : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Matrix.swap ℂ i j * M * Matrix.swap ℂ i j) a b = M (Equiv.swap i j a) (Equiv.swap i j b) := by
  rw [Matrix.swap, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap]
  rfl

theorem transvection_mul_single_self (i j b : Fin n) (z x : ℂ) :
    Matrix.transvection i j z * Matrix.single j b x =
      Matrix.single j b x + Matrix.single i b (z * x) := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.single_mul_single_same]

theorem transvection_mul_single_of_ne (i j : Fin n) {a : Fin n} (ha : a ≠ j) (b : Fin n)
    (z x : ℂ) : Matrix.transvection i j z * Matrix.single a b x = Matrix.single a b x := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm ha) _, add_zero]

theorem single_mul_transvection_self (i j a : Fin n) (z x : ℂ) :
    Matrix.single a i x * Matrix.transvection i j z =
      Matrix.single a i x + Matrix.single a j (x * z) := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.single_mul_single_same]

theorem single_mul_transvection_of_ne (i j a : Fin n) {b : Fin n} (hb : b ≠ i) (z x : ℂ) :
    Matrix.single a b x * Matrix.transvection i j z = Matrix.single a b x := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hb _, add_zero]

variable (hj : (j : ℕ) = i + 1)
include hj

theorem lt_of_val_eq_succ : i < j := by
  rw [Fin.lt_def]
  omega

/-- `C(z) (w E_ij) = s (w E_ij) = w E_jj`. -/
theorem chart_mul_single_ij (z w : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i j w =
      Matrix.swap ℂ i j * Matrix.single i j w := by
  rw [Matrix.mul_assoc, transvection_mul_single_of_ne i j (ne_of_val_eq_succ hj) j z w]

theorem chart_mul_single_ij' (z w : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i j w = Matrix.single j j w := by
  rw [chart_mul_single_ij hj, swap_mul_single, Equiv.swap_apply_left]

/-- `C(z) (c E_jj) = (c E_ii) C(z) + C(z) (c z E_ij)`. -/
theorem chart_mul_single_jj (z c : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single j j c =
      Matrix.single i i c * (Matrix.swap ℂ i j * Matrix.transvection i j z) +
        Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i j (c * z) := by
  have hji : j ≠ i := (ne_of_val_eq_succ hj).symm
  have e1 : Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single j j c =
      Matrix.single i j c + Matrix.single j j (z * c) := by
    rw [Matrix.mul_assoc, transvection_mul_single_self, Matrix.mul_add, swap_mul_single,
      swap_mul_single, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have e2 : Matrix.single i i c * (Matrix.swap ℂ i j * Matrix.transvection i j z) =
      Matrix.single i j c := by
    rw [← Matrix.mul_assoc, single_mul_swap, Equiv.swap_apply_left,
      single_mul_transvection_of_ne i j i hji]
  rw [e1, e2, chart_mul_single_ij' hj, mul_comm z c]

/-- `C(z) (c E_ii) = (c E_jj) C(z) - C(z) (c z E_ij)`. -/
theorem chart_mul_single_ii (z c : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i i c =
      Matrix.single j j c * (Matrix.swap ℂ i j * Matrix.transvection i j z) -
        Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i j (c * z) := by
  have e1 : Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single i i c =
      Matrix.single j i c := by
    rw [Matrix.mul_assoc, transvection_mul_single_of_ne i j (ne_of_val_eq_succ hj) i z c,
      swap_mul_single, Equiv.swap_apply_left]
  have e2 : Matrix.single j j c * (Matrix.swap ℂ i j * Matrix.transvection i j z) =
      Matrix.single j i c + Matrix.single j j (c * z) := by
    rw [← Matrix.mul_assoc, single_mul_swap, Equiv.swap_apply_right,
      single_mul_transvection_self]
  rw [e1, e2, chart_mul_single_ij' hj, add_sub_cancel_right]

omit hj in
/-- `E_kk` commutes with `C(z)` for `k ≠ i, j`. -/
theorem chart_mul_single_kk {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (z c : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.single k k c =
      Matrix.single k k c * (Matrix.swap ℂ i j * Matrix.transvection i j z) := by
  rw [Matrix.mul_assoc, transvection_mul_single_of_ne i j hkj k z c, swap_mul_single,
    Equiv.swap_apply_of_ne_of_ne hki hkj, ← Matrix.mul_assoc, single_mul_swap,
    Equiv.swap_apply_of_ne_of_ne hki hkj, single_mul_transvection_of_ne i j k hki z c]

omit hj in
theorem swap_le_or {a b : Fin n} (hj : (j : ℕ) = i + 1) (hab : b ≤ a) :
    Equiv.swap i j b ≤ Equiv.swap i j a ∨ (Equiv.swap i j a = i ∧ Equiv.swap i j b = j) := by
  have hs : ∀ x : Fin n, ((Equiv.swap i j x : Fin n) : ℕ) =
      (if (x : ℕ) = i then j else if (x : ℕ) = j then i else x : ℕ) := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]
  rw [Fin.le_iff_val_le_val] at hab
  rw [Fin.le_iff_val_le_val, Fin.ext_iff, Fin.ext_iff, hs a, hs b]
  split_ifs <;> omega

/-- `x(z) X x(-z)` vanishes on and below the diagonal and at `(i, j)` when `X` is strictly upper
triangular with `X_ij = 0`. -/
theorem transvection_conj_apply_eq_zero {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) (hXij : X i j = 0) (z : ℂ) {p q : Fin n}
    (hpq : q ≤ p ∨ (p = i ∧ q = j)) :
    (Matrix.transvection i j z * X * Matrix.transvection i j (-z)) p q = 0 := by
  have hlt := lt_of_val_eq_succ hj
  have h1 : X p q = 0 := by
    rcases hpq with h | ⟨rfl, rfl⟩
    · exact hX p q h
    · exact hXij
  have h2 : (Matrix.single i j z * X) p q = 0 := by
    by_cases hp : p = i
    · rw [hp, Matrix.single_mul_apply_same]
      have hq : q ≤ j := by
        rcases hpq with h | ⟨_, rfl⟩
        · exact le_trans (hp ▸ h) hlt.le
        · exact le_rfl
      rw [hX j q hq, mul_zero]
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ hp _
  have h3 : (X * Matrix.single i j (-z)) p q = 0 := by
    by_cases hq : q = j
    · rw [hq, Matrix.mul_single_apply_same]
      have hp : i ≤ p := by
        rcases hpq with h | ⟨rfl, _⟩
        · exact le_trans hlt.le (hq ▸ h)
        · exact le_rfl
      rw [hX p i hp, zero_mul]
    · exact Matrix.mul_single_apply_of_ne _ _ _ _ _ hq _
  have h4 : X j i = 0 := hX j i hlt.le
  simp only [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.add_apply, Matrix.single_mul_mul_single, h1, h2, h3, h4]
  simp

end Algebra

/-! ## Right derivatives along the chart -/

section Derivatives

variable {ds : List ComplexCharacterData} (hn : ds.length = n) {i j : Fin n}
  (hj : (j : ℕ) = i + 1) {f : Langlands.GeneralLinear n ℂ → ℂ}
  (hf : f ∈ complexStandardModule n ds)

/-- The real-linear map `w ↦ w E_ij`. -/
def singleCLM (i j : Fin n) : ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (Matrix.single i j (1 : ℂ))

theorem singleCLM_apply (i j : Fin n) (w : ℂ) : singleCLM i j w = Matrix.single i j w := by
  rw [singleCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem transvection_eq_add_singleCLM (i j : Fin n) (z : ℂ) :
    Matrix.transvection i j z = 1 + singleCLM i j z := by
  rw [singleCLM_apply, Matrix.transvection]

theorem hasFDerivAt_chartMatrix (i j : Fin n) (z : ℂ) :
    HasFDerivAt (fun z : ℂ => Matrix.swap ℂ i j * Matrix.transvection i j z)
      (Matrix.swap ℂ i j • singleCLM i j) z := by
  simp only [transvection_eq_add_singleCLM]
  exact ((singleCLM i j).hasFDerivAt.const_add 1).const_mul (Matrix.swap ℂ i j)

theorem contDiff_chartMatrix (i j : Fin n) :
    ContDiff ℝ ∞ (fun z : ℂ => Matrix.swap ℂ i j * Matrix.transvection i j z) := by
  simp only [transvection_eq_add_singleCLM]
  exact contDiff_const.mul (contDiff_const.add (singleCLM i j).contDiff)

include hj in
theorem chartRestrict_eq_comp :
    (fun z => f (chart i j hj z)) =
      unitsExtension f ∘ (fun z : ℂ => Matrix.swap ℂ i j * Matrix.transvection i j z) :=
  funext fun z => (unitsExtension_val f (chart i j hj z)).symm

/-- (P1) The restriction `φ(z) = f(C(z))` of a smooth function is smooth. -/
theorem contDiff_chartRestrict (hfs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) :
    ContDiff ℝ ∞ (fun z => f (chart i j hj z)) := by
  rw [chartRestrict_eq_comp hj]
  exact (contDiffOn_unitsExtension hfs).comp_contDiff (contDiff_chartMatrix i j)
    fun z => Units.isUnit (chart i j hj z)

/-- (P3) `R(w E_ij) f (C(z)) = Dφ(z)(w)`. -/
theorem rightDerivative_chart_single_ij (hfs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f)
    (w z : ℂ) :
    rightDerivative (matrixModel ℂ n) (Matrix.single i j w) f (chart i j hj z) =
      fderiv ℝ (fun z => f (chart i j hj z)) z w := by
  have hd := (differentiableAt_unitsExtension hfs (Units.isUnit (chart i j hj z))).hasFDerivAt
  have hcomp := hd.comp z (hasFDerivAt_chartMatrix i j z)
  rw [rightDerivative_eq_fderiv hfs, chartRestrict_eq_comp hj, hcomp.fderiv, chart_val,
    chart_mul_single_ij hj]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, singleCLM_apply, smul_eq_mul]

include hf in
/-- (P2) `R(X) f (C(z)) = 0` for `X` strictly upper triangular with `X_ij = 0`. -/
theorem rightDerivative_chart_strictUpper (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) (hXij : X i j = 0) (z : ℂ) :
    rightDerivative (matrixModel ℂ n) X f (chart i j hj z) = 0 := by
  have hij := ne_of_val_eq_succ hj
  set N : Matrix (Fin n) (Fin n) ℂ := Matrix.swap ℂ i j *
    (Matrix.transvection i j z * X * Matrix.transvection i j (-z)) * Matrix.swap ℂ i j with hN
  have hNC : Matrix.swap ℂ i j * Matrix.transvection i j z * X =
      N * (Matrix.swap ℂ i j * Matrix.transvection i j z) := by
    calc Matrix.swap ℂ i j * Matrix.transvection i j z * X
        = Matrix.swap ℂ i j * (Matrix.transvection i j z * X) *
            (Matrix.transvection i j (-z) * Matrix.transvection i j z) := by
          rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel,
            Matrix.transvection_zero, Matrix.mul_one, Matrix.mul_assoc]
      _ = Matrix.swap ℂ i j * (Matrix.transvection i j z * X * Matrix.transvection i j (-z)) *
            (Matrix.swap ℂ i j * Matrix.swap ℂ i j) * Matrix.transvection i j z := by
          rw [Matrix.swap_mul_self, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = N * (Matrix.swap ℂ i j * Matrix.transvection i j z) := by
          rw [hN]
          simp only [Matrix.mul_assoc]
  have hNup : ∀ a b : Fin n, b ≤ a → N a b = 0 := by
    intro a b hab
    rw [hN, swap_mul_mul_swap_apply]
    exact transvection_conj_apply_eq_zero hj hX hXij z (swap_le_or hj hab)
  rw [rightDerivative_eq_fderiv hf.1, chart_val, hNC]
  exact ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero
    (differentiableAt_unitsExtension hf.1 (Units.isUnit (chart i j hj z)))
    (fun u => unitsExtension_unipotent_mul_eq hf u (chart i j hj z)) hNup

include hf in
/-- (P4) `R(c E_kk) f (C(z)) = κ_k(c) f(C(z))` for `k ≠ i, j`. -/
theorem rightDerivative_chart_diag_other (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) (c z : ℂ) :
    rightDerivative (matrixModel ℂ n) (Matrix.single k k c) f (chart i j hj z) =
      kappa ds hn k c * f (chart i j hj z) := by
  rw [rightDerivative_eq_fderiv hf.1, ← fderiv_unitsExtension_single_mul hn hf k c (chart i j hj z),
    chart_val, chart_mul_single_kk hki hkj]

include hf in
/-- (P5) `R(c E_jj) f (C(z)) = κ_i(c) f(C(z)) + Dφ(z)(c z)`. -/
theorem rightDerivative_chart_diag_j (c z : ℂ) :
    rightDerivative (matrixModel ℂ n) (Matrix.single j j c) f (chart i j hj z) =
      kappa ds hn i c * f (chart i j hj z) + fderiv ℝ (fun z => f (chart i j hj z)) z (c * z) := by
  rw [← rightDerivative_chart_single_ij hj hf.1 (c * z) z, rightDerivative_eq_fderiv hf.1,
    rightDerivative_eq_fderiv hf.1, ← fderiv_unitsExtension_single_mul hn hf i c (chart i j hj z),
    ← map_add, chart_val, chart_mul_single_jj hj]

include hf in
/-- (P6) `R(c E_ii) f (C(z)) = κ_j(c) f(C(z)) - Dφ(z)(c z)`. -/
theorem rightDerivative_chart_diag_i (c z : ℂ) :
    rightDerivative (matrixModel ℂ n) (Matrix.single i i c) f (chart i j hj z) =
      kappa ds hn j c * f (chart i j hj z) - fderiv ℝ (fun z => f (chart i j hj z)) z (c * z) := by
  rw [← rightDerivative_chart_single_ij hj hf.1 (c * z) z, rightDerivative_eq_fderiv hf.1,
    rightDerivative_eq_fderiv hf.1, ← fderiv_unitsExtension_single_mul hn hf j c (chart i j hj z),
    ← map_sub, chart_val, chart_mul_single_ii hj]

end Derivatives

section Identity

variable {ds : List ComplexCharacterData} (hn : ds.length = n)
  {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)

include hf in
/-- (P7a) `R(X) f (1) = 0` for `X` strictly upper triangular. -/
theorem rightDerivative_one_strictUpper (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b : Fin n, b ≤ a → X a b = 0) :
    rightDerivative (matrixModel ℂ n) X f 1 = 0 := by
  have h := ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero
    (differentiableAt_unitsExtension hf.1 (Units.isUnit (1 : Langlands.GeneralLinear n ℂ)))
    (fun u => unitsExtension_unipotent_mul_eq hf u 1) hX
  rw [rightDerivative_eq_fderiv hf.1]
  rwa [Units.val_one, Matrix.mul_one, Matrix.one_mul] at *

include hf in
/-- (P7b) `R(c E_kk) f (1) = κ_k(c) f(1)`. -/
theorem rightDerivative_one_diag (k : Fin n) (c : ℂ) :
    rightDerivative (matrixModel ℂ n) (Matrix.single k k c) f 1 = kappa ds hn k c * f 1 := by
  rw [rightDerivative_eq_fderiv hf.1, ← fderiv_unitsExtension_single_mul hn hf k c 1,
    Units.val_one, Matrix.one_mul, Matrix.mul_one]

end Identity

end Langlands.Archimedean.ComplexSwapJacquet
