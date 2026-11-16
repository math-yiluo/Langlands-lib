import Langlands.Representation.Archimedean.ComplexMomentSymbols
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Top symbols of words of first-order operators

On the polynomials `Pol n` in the coordinates `v` and the dual coordinates `ξ`, consider first-order
operators `op d = Σ_p W_p ∂_{v_p} + λ` (`d : OpData n`) and their compositions along words
`w = [d₁, …, d_k]` (`evalWord w = op d₁ ∘ ⋯ ∘ op d_k`). With `ℓ = Σ_p v_p ξ_p`,
`evalWord w (ℓ^m) = Σ_{j ≤ m} m(m-1)⋯(m-j+1) ℓ^{m-j} c_j(w)` (`evalWord_ell_pow`), where the top
coefficient `c_k(w)` is the product of the symbols `sym d = Σ_p W_p ξ_p` (`wcoeff_length`).
Hence a vanishing linear combination of words has vanishing combined coefficients
(`sum_wcoeff_eq_zero`), in particular a vanishing combination of the symbol products of its
longest words. `eq_zero_of_kills_rename`: an operator built from words vanishes on `Pol n` as
soon as it vanishes on the polynomials in `v` alone.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.MomentSymbols

open MvPolynomial Langlands.Archimedean.NoncompactPicture

variable {n : ℕ}

theorem xV_ne_vV (q p : Lw n) : xV q ≠ vV p := Sum.inr_ne_inl

theorem vV_injective : Function.Injective (vV (n := n)) := Sum.inl_injective

@[simp] theorem pderiv_vV_X_xV (p q : Lw n) : pderiv (vV p) (X (xV q) : Pol n) = 0 :=
  pderiv_X_of_ne (xV_ne_vV q p)

/-- The data `(W, λ)` of a first-order operator `Σ_p W_p ∂_{v_p} + λ`. -/
structure OpData (n : ℕ) where
  /-- The coefficients of the derivatives. -/
  W : Lw n → Pol n
  /-- The multiplication term. -/
  lam : Pol n

/-- The operator `Σ_p W_p ∂_{v_p} + λ`. -/
def op (d : OpData n) : Pol n →ₗ[ℂ] Pol n :=
  (∑ p, LinearMap.mulLeft ℂ (d.W p) ∘ₗ (pderiv (vV p)).toLinearMap) + LinearMap.mulLeft ℂ d.lam

theorem op_apply (d : OpData n) (P : Pol n) :
    op d P = ∑ p, d.W p * pderiv (vV p) P + d.lam * P := by
  simp [op, LinearMap.sum_apply]

/-- The symbol `Σ_p W_p ξ_p`. -/
def sym (d : OpData n) : Pol n := ∑ p, d.W p * X (xV p)

/-- `ℓ = Σ_p v_p ξ_p`. -/
def ellF : Pol n := ∑ q, X (vV q) * X (xV q)

theorem pderiv_ellF (p : Lw n) : pderiv (vV p) (ellF (n := n)) = X (xV p) := by
  classical
  rw [ellF, map_sum, Finset.sum_eq_single p]
  · rw [pderiv_mul, pderiv_X_self, pderiv_vV_X_xV, one_mul, mul_zero, add_zero]
  · intro q _ hq
    rw [pderiv_mul, pderiv_X_of_ne (fun h => hq (vV_injective h)), pderiv_vV_X_xV, zero_mul,
      mul_zero, add_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem op_ell_pow_mul (d : OpData n) (r : ℕ) (P : Pol n) :
    op d (ellF ^ r * P) = ellF ^ r * op d P + r • (ellF ^ (r - 1) * (sym d * P)) := by
  rw [op_apply, op_apply, sym, nsmul_eq_mul]
  have e1 : ∑ p, d.W p * pderiv (vV p) (ellF ^ r * P) =
      (r : Pol n) * (ellF ^ (r - 1) * ((∑ p, d.W p * X (xV p)) * P)) +
        ellF ^ r * ∑ p, d.W p * pderiv (vV p) P := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pderiv_mul, pderiv_pow, pderiv_ellF]
    ring
  rw [e1]
  ring

/-- The composition of the operators of a word. -/
def evalWord : List (OpData n) → Pol n →ₗ[ℂ] Pol n
  | [] => LinearMap.id
  | d :: w => op d ∘ₗ evalWord w

/-- The coefficients of `evalWord w (ℓ^m)`. -/
def wcoeff : List (OpData n) → ℕ → Pol n
  | [], j => if j = 0 then 1 else 0
  | d :: w, j => op d (wcoeff w j) + if j = 0 then 0 else sym d * wcoeff w (j - 1)

/-- **The expansion of `evalWord w (ℓ^m)`.** -/
theorem evalWord_ell_pow (w : List (OpData n)) (m : ℕ) :
    evalWord w (ellF ^ m) =
      ∑ j ∈ Finset.range (m + 1), m.descFactorial j • (ellF ^ (m - j) * wcoeff w j) := by
  induction w with
  | nil =>
    rw [Finset.sum_eq_single 0]
    · simp [evalWord, wcoeff]
    · intro j _ hj
      simp [wcoeff, hj]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) h
  | cons d w ih =>
    change op d (evalWord w (ellF ^ m)) = _
    rw [ih, map_sum]
    simp only [map_nsmul, op_ell_pow_mul, smul_add, Finset.sum_add_distrib, wcoeff, mul_add]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_self, zero_smul, smul_zero, add_zero,
      ite_eq_left rfl, mul_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := Finset.mem_range.1 hj
    rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, Nat.descFactorial_succ, smul_smul,
      show m - (j + 1) = m - j - 1 by omega, mul_comm (m - j)]

theorem wcoeff_eq_zero_of_lt : ∀ (w : List (OpData n)) (j : ℕ), w.length < j → wcoeff w j = 0
  | [], j, h => by simp [wcoeff, Nat.pos_iff_ne_zero.1 h]
  | d :: w, j, h => by
    simp only [List.length_cons] at h
    rw [wcoeff, wcoeff_eq_zero_of_lt w j (by omega), map_zero, zero_add,
      ite_eq_right (by omega), wcoeff_eq_zero_of_lt w (j - 1) (by omega), mul_zero]

/-- **The top coefficient is the product of the symbols.** -/
theorem wcoeff_length : ∀ w : List (OpData n), wcoeff w w.length = (w.map sym).prod
  | [] => by simp [wcoeff]
  | d :: w => by
    rw [List.length_cons, wcoeff, wcoeff_eq_zero_of_lt w _ (Nat.lt_succ_self _), map_zero, zero_add,
      ite_eq_right (Nat.succ_ne_zero _), Nat.add_sub_cancel, wcoeff_length w, List.map_cons,
      List.prod_cons]

/-- **A vanishing combination of words has vanishing combined coefficients.** -/
theorem sum_wcoeff_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → List (OpData n))
    (h : ∀ P, ∑ i ∈ s, c i • evalWord (w i) P = 0) (j : ℕ) :
    ∑ i ∈ s, c i • wcoeff (w i) j = 0 := by
  set Q : ℕ → Pol n := fun j => ∑ i ∈ s, c i • wcoeff (w i) j
  have hexp : ∀ m, ∑ j ∈ Finset.range (m + 1), m.descFactorial j • (ellF ^ (m - j) * Q j) = 0 := by
    intro m
    have := h (ellF ^ m)
    simp only [evalWord_ell_pow, Finset.smul_sum] at this
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Q, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_comm (c _)]
  show Q j = 0
  induction j using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := hexp m
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [ih i (Finset.mem_range.1 hi), mul_zero, smul_zero], zero_add, Nat.sub_self, pow_zero,
      one_mul, Nat.descFactorial_self] at h1
    have h2 : ((m.factorial : ℂ)) • Q m = 0 := by
      rw [Nat.cast_smul_eq_nsmul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left (by exact_mod_cast m.factorial_ne_zero)

/-- **The longest words.** If the words have length `≤ K`, a vanishing combination gives a
vanishing combination of the symbol products of the words of length `K`. -/
theorem sum_prod_sym_eq_zero {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → List (OpData n))
    (h : ∀ P, ∑ i ∈ s, c i • evalWord (w i) P = 0) (K : ℕ) (hK : ∀ i ∈ s, (w i).length ≤ K) :
    ∑ i ∈ s.filter (fun i => (w i).length = K), c i • ((w i).map sym).prod = 0 := by
  classical
  have := sum_wcoeff_eq_zero s c w h K
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => (w i).length = K)] at this
  rw [Finset.sum_eq_zero (s := s.filter fun i => ¬ (w i).length = K) fun i hi => by
    obtain ⟨his, hne⟩ := Finset.mem_filter.1 hi
    rw [wcoeff_eq_zero_of_lt _ _ (lt_of_le_of_ne (hK i his) hne), smul_zero], add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← (Finset.mem_filter.1 hi).2, wcoeff_length]

/-! ## Operators vanishing on the polynomials in `v` -/

theorem op_xV_mul (d : OpData n) (q : Lw n) (P : Pol n) :
    op d (X (xV q) * P) = X (xV q) * op d P := by
  rw [op_apply, op_apply, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [pderiv_mul, pderiv_vV_X_xV, zero_mul, zero_add]
    ring
  · ring

theorem evalWord_xV_mul : ∀ (w : List (OpData n)) (q : Lw n) (P : Pol n),
    evalWord w (X (xV q) * P) = X (xV q) * evalWord w P
  | [], q, P => rfl
  | d :: w, q, P => by
    change op d (evalWord w _) = X (xV q) * op d (evalWord w P)
    rw [evalWord_xV_mul w q P, op_xV_mul]

/-- **Vanishing on the polynomials in `v` suffices.** -/
theorem eq_zero_of_kills_rename {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (w : ι → List (OpData n))
    (h : ∀ Q : MvPolynomial (Lw n) ℂ, ∑ i ∈ s, c i • evalWord (w i) (rename vV Q) = 0) :
    ∀ P : Pol n, ∑ i ∈ s, c i • evalWord (w i) P = 0 := by
  have key : ∀ P : Pol n, ∀ Q : MvPolynomial (Lw n) ℂ,
      ∑ i ∈ s, c i • evalWord (w i) (P * rename vV Q) = 0 := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      intro Q
      have := h (C a * Q)
      rwa [map_mul, rename_C] at this
    | add P₁ P₂ h₁ h₂ =>
      intro Q
      simp only [add_mul, map_add, smul_add, Finset.sum_add_distrib, h₁ Q, h₂ Q, add_zero]
    | mul_X P x ih =>
      intro Q
      rcases x with p | q
      · have := ih (X p * Q)
        rwa [map_mul, rename_X, ← mul_assoc] at this
      · show ∑ i ∈ s, c i • evalWord (w i) (P * X (xV q) * rename vV Q) = 0
        have : P * X (xV q) * rename vV Q = X (xV q) * (P * rename vV Q) := by ring
        rw [this]
        simp only [evalWord_xV_mul]
        have e : ∀ x ∈ s, c x • (X (xV q) * evalWord (w x) (P * rename vV Q)) =
            X (xV q) * (c x • evalWord (w x) (P * rename vV Q)) := fun x _ => (mul_smul_comm _ _ _).symm
        rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ih Q, mul_zero]
  intro P
  simpa using key P 1

end Langlands.Archimedean.MomentSymbols
