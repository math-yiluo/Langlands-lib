import Mathlib

/-!
# Polynomial algebra for the irreducibility of `GL_2(ℂ)` principal series

Polynomials in `r_0, r_1` and their conjugates, written `z 0, z 1, w 0, w 1`, with the
partial derivatives `dz k = ∂/∂z_k`, `dw k = ∂/∂w_k`, the Euler operators `EZ`, `EW`, the
Laplacian `Lap = Σ_k dz k ∘ dw k`, the operators `D i k = z_i ∂_{z_k} - w_k ∂_{w_i}` of the
complexified Lie algebra of `U(2)`, and the eigenspaces `Eig a b` of `(EZ, EW)`.
-/

noncomputable section

open MvPolynomial

set_option autoImplicit false

namespace Langlands.Archimedean.GLTwoPoly

/-- The variables: `Sum.inl k` stands for `r_k`, `Sum.inr k` for its complex conjugate. -/
abbrev Var := Fin 2 ⊕ Fin 2

/-- Polynomials in `r_0, r_1, r̄_0, r̄_1`. -/
abbrev Pol := MvPolynomial Var ℂ

/-- The coordinate `r_k`. -/
def z (k : Fin 2) : Pol := X (Sum.inl k)

/-- The conjugate coordinate `r̄_k`. -/
def w (k : Fin 2) : Pol := X (Sum.inr k)

/-- `N = r_0 r̄_0 + r_1 r̄_1 = |r|²`. -/
def N : Pol := z 0 * w 0 + z 1 * w 1

/-- `∂/∂z_k`. -/
def dz (k : Fin 2) (P : Pol) : Pol := pderiv (Sum.inl k) P

/-- `∂/∂w_k`. -/
def dw (k : Fin 2) (P : Pol) : Pol := pderiv (Sum.inr k) P

/-! ## Leibniz rules -/

theorem dz_add (k : Fin 2) (P Q : Pol) : dz k (P + Q) = dz k P + dz k Q := map_add _ _ _
theorem dw_add (k : Fin 2) (P Q : Pol) : dw k (P + Q) = dw k P + dw k Q := map_add _ _ _
theorem dz_sub (k : Fin 2) (P Q : Pol) : dz k (P - Q) = dz k P - dz k Q := map_sub _ _ _
theorem dw_sub (k : Fin 2) (P Q : Pol) : dw k (P - Q) = dw k P - dw k Q := map_sub _ _ _
theorem dz_mul (k : Fin 2) (P Q : Pol) : dz k (P * Q) = dz k P * Q + P * dz k Q := pderiv_mul
theorem dw_mul (k : Fin 2) (P Q : Pol) : dw k (P * Q) = dw k P * Q + P * dw k Q := pderiv_mul
theorem dz_C (k : Fin 2) (a : ℂ) : dz k (C a) = 0 := pderiv_C
theorem dw_C (k : Fin 2) (a : ℂ) : dw k (C a) = 0 := pderiv_C
theorem dz_zero (k : Fin 2) : dz k 0 = 0 := map_zero _
theorem dw_zero (k : Fin 2) : dw k 0 = 0 := map_zero _
theorem dz_C_mul (k : Fin 2) (a : ℂ) (P : Pol) : dz k (C a * P) = C a * dz k P := pderiv_C_mul
theorem dw_C_mul (k : Fin 2) (a : ℂ) (P : Pol) : dw k (C a * P) = C a * dw k P := pderiv_C_mul

theorem dz_z (k i : Fin 2) : dz k (z i) = if i = k then 1 else 0 := by
  unfold dz z
  split_ifs with h
  · subst h; exact pderiv_X_self _
  · exact pderiv_X_of_ne (by simpa using h)

theorem dz_w (k i : Fin 2) : dz k (w i) = 0 := pderiv_X_of_ne (by simp)

theorem dw_z (k i : Fin 2) : dw k (z i) = 0 := pderiv_X_of_ne (by simp)

theorem dw_w (k i : Fin 2) : dw k (w i) = if i = k then 1 else 0 := by
  unfold dw w
  split_ifs with h
  · subst h; exact pderiv_X_self _
  · exact pderiv_X_of_ne (by simpa using h)

/-- Partial derivatives commute. -/
theorem pderiv_comm (i j : Var) (P : Pol) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [pderiv_mul, map_add, pderiv_X, hp]
    by_cases hi : i = n <;> by_cases hj : j = n <;> simp [hi, hj]

theorem dz_dz (k l : Fin 2) (P : Pol) : dz k (dz l P) = dz l (dz k P) := pderiv_comm _ _ _
theorem dw_dw (k l : Fin 2) (P : Pol) : dw k (dw l P) = dw l (dw k P) := pderiv_comm _ _ _
theorem dz_dw (k l : Fin 2) (P : Pol) : dz k (dw l P) = dw l (dz k P) := pderiv_comm _ _ _

/-- The simp set expanding derivatives of polynomial expressions. -/
theorem dz_N (k : Fin 2) : dz k N = w k := by
  fin_cases k <;> simp [N, dz_add, dz_mul, dz_z, dz_w]

theorem dw_N (k : Fin 2) : dw k N = z k := by
  fin_cases k <;> simp [N, dw_add, dw_mul, dw_z, dw_w]

/-! ## Euler operators, Laplacian and the operators `D i k` -/

/-- `EZ = z_0 ∂_{z_0} + z_1 ∂_{z_1}`. -/
def EZ (P : Pol) : Pol := z 0 * dz 0 P + z 1 * dz 1 P

/-- `EW = w_0 ∂_{w_0} + w_1 ∂_{w_1}`. -/
def EW (P : Pol) : Pol := w 0 * dw 0 P + w 1 * dw 1 P

/-- The Laplacian `Δ = Σ_k ∂_{z_k} ∂_{w_k}`. -/
def Lap (P : Pol) : Pol := dz 0 (dw 0 P) + dz 1 (dw 1 P)

/-- `D i k = z_i ∂_{z_k} - w_k ∂_{w_i}`. -/
def D (i k : Fin 2) (P : Pol) : Pol := z i * dz k P - w k * dw i P

/-- The joint eigenspace `EZ = a`, `EW = b`. -/
def Eig (a b : ℂ) : Submodule ℂ Pol where
  carrier := {P | EZ P = C a * P ∧ EW P = C b * P}
  zero_mem' := by simp [EZ, EW, dz_zero, dw_zero]
  add_mem' {P Q} hP hQ := by
    obtain ⟨h1, h2⟩ := hP
    obtain ⟨h3, h4⟩ := hQ
    refine ⟨?_, ?_⟩
    · simp only [EZ, dz_add] at h1 h3 ⊢; linear_combination h1 + h3
    · simp only [EW, dw_add] at h2 h4 ⊢; linear_combination h2 + h4
  smul_mem' c P hP := by
    obtain ⟨h1, h2⟩ := hP
    simp only [Set.mem_ofPred_eq, smul_eq_C_mul, EZ, EW, dz_C_mul, dw_C_mul] at h1 h2 ⊢
    refine ⟨?_, ?_⟩
    · linear_combination C c * h1
    · linear_combination C c * h2

theorem mem_Eig {a b : ℂ} {P : Pol} : P ∈ Eig a b ↔ EZ P = C a * P ∧ EW P = C b * P :=
  Iff.rfl

/-! ## Commutation with the Euler operators -/

theorem EZ_z_mul (k : Fin 2) (P : Pol) : EZ (z k * P) = z k * P + z k * EZ P := by
  fin_cases k <;> simp [EZ, dz_mul, dz_z] <;> ring

theorem EW_z_mul (k : Fin 2) (P : Pol) : EW (z k * P) = z k * EW P := by
  simp [EW, dw_mul, dw_z]; ring

theorem EZ_w_mul (k : Fin 2) (P : Pol) : EZ (w k * P) = w k * EZ P := by
  simp [EZ, dz_mul, dz_w]; ring

theorem EW_w_mul (k : Fin 2) (P : Pol) : EW (w k * P) = w k * P + w k * EW P := by
  fin_cases k <;> simp [EW, dw_mul, dw_w] <;> ring

theorem EZ_dz (k : Fin 2) (P : Pol) : EZ (dz k P) = dz k (EZ P) - dz k P := by
  fin_cases k <;> simp [EZ, dz_add, dz_mul, dz_z, dz_dz 0 1] <;> ring

theorem EW_dz (k : Fin 2) (P : Pol) : EW (dz k P) = dz k (EW P) := by
  simp [EW, dz_add, dz_mul, dz_w, dz_dw]

theorem EZ_dw (k : Fin 2) (P : Pol) : EZ (dw k P) = dw k (EZ P) := by
  simp [EZ, dw_add, dw_mul, dw_z, dz_dw]

theorem EW_dw (k : Fin 2) (P : Pol) : EW (dw k P) = dw k (EW P) - dw k P := by
  fin_cases k <;> simp [EW, dw_add, dw_mul, dw_w, dw_dw 0 1] <;> ring

/-! ## Closure of the eigenspaces -/

theorem z_mul_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) (k : Fin 2) :
    z k * P ∈ Eig (a + 1) b := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [EZ_z_mul, h1, map_add, map_one]; ring
  · rw [EW_z_mul, h2]; ring

theorem w_mul_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) (k : Fin 2) :
    w k * P ∈ Eig a (b + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [EZ_w_mul, h1]; ring
  · rw [EW_w_mul, h2, map_add, map_one]; ring

theorem dz_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) (k : Fin 2) :
    dz k P ∈ Eig (a - 1) b := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [EZ_dz, h1, dz_C_mul, map_sub, map_one]; ring
  · rw [EW_dz, h2, dz_C_mul]

theorem dw_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) (k : Fin 2) :
    dw k P ∈ Eig a (b - 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [EZ_dw, h1, dw_C_mul]
  · rw [EW_dw, h2, dw_C_mul, map_sub, map_one]; ring

theorem N_mul_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) : N * P ∈ Eig (a + 1) (b + 1) := by
  have e : N * P = z 0 * (w 0 * P) + z 1 * (w 1 * P) := by unfold N; ring
  rw [e]
  exact add_mem (z_mul_mem (w_mul_mem h 0) 0) (z_mul_mem (w_mul_mem h 1) 1)

theorem Lap_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) : Lap P ∈ Eig (a - 1) (b - 1) :=
  add_mem (dz_mem (dw_mem h 0) 0) (dz_mem (dw_mem h 1) 1)

theorem D_mem {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) (i k : Fin 2) : D i k P ∈ Eig a b := by
  have h1 := z_mul_mem (dz_mem h k) i
  have h2 := w_mul_mem (dw_mem h i) k
  rw [sub_add_cancel] at h1 h2
  exact sub_mem h1 h2

/-! ## The Casimir operator of `𝔰𝔩_2` -/

theorem D_add (i k : Fin 2) (P Q : Pol) : D i k (P + Q) = D i k P + D i k Q := by
  simp [D, dz_add, dw_add]; ring

theorem D_sub (i k : Fin 2) (P Q : Pol) : D i k (P - Q) = D i k P - D i k Q := by
  simp [D, dz_sub, dw_sub]; ring

theorem D_C_mul (i k : Fin 2) (c : ℂ) (P : Pol) : D i k (C c * P) = C c * D i k P := by
  simp [D, dz_C_mul, dw_C_mul]; ring

/-- `D i k (D k i P)`, expanded. -/
theorem D_D (i k : Fin 2) (P : Pol) :
    D i k (D k i P) = z i * dz i P + z i * z k * dz k (dz i P) - z i * w i * dz k (dw k P) -
      w k * z k * dz i (dw i P) + w k * dw k P + w k * w i * dw i (dw k P) := by
  simp only [D, dz_sub, dz_mul, dw_sub, dw_mul, dz_z, dz_w, dw_z, dw_w, ite_true, dz_dw]
  ring

/-- Twice the Casimir operator of `𝔰𝔩_2` in the operators `D i k`:
`2 (D₀₁ D₁₀ + D₁₀ D₀₁) + (D₀₀ - D₁₁)²`. -/
def Cas (P : Pol) : Pol :=
  2 * D 0 1 (D 1 0 P) + 2 * D 1 0 (D 0 1 P) +
    (D 0 0 (D 0 0 P - D 1 1 P) - D 1 1 (D 0 0 P - D 1 1 P))

/-- The eigenvalue `2a(a+1) + 2b(b+1) - (a-b)²` of `Cas` on harmonic polynomials in
`Eig a b`. -/
def casValue (a b : ℂ) : ℂ := 2 * a * (a + 1) + 2 * b * (b + 1) - (a - b) ^ 2

theorem Cas_eq {a b : ℂ} {P : Pol} (h : P ∈ Eig a b) :
    Cas P = C (casValue a b) * P - 4 * (N * Lap P) := by
  obtain ⟨hZ, hW⟩ := h
  obtain ⟨hZ0, -⟩ := dz_mem ⟨hZ, hW⟩ 0
  obtain ⟨hZ1, -⟩ := dz_mem ⟨hZ, hW⟩ 1
  obtain ⟨-, hW0⟩ := dw_mem ⟨hZ, hW⟩ 0
  obtain ⟨-, hW1⟩ := dw_mem ⟨hZ, hW⟩ 1
  simp only [EZ, EW] at hZ hW hZ0 hZ1 hW0 hW1
  have e00 := D_D 0 0 P
  have e11 := D_D 1 1 P
  have e01 := D_D 0 1 P
  have e10 := D_D 1 0 P
  have h00 : D 0 0 (D 0 0 P - D 1 1 P) - D 1 1 (D 0 0 P - D 1 1 P) =
      2 * (D 0 0 (D 0 0 P) + D 1 1 (D 1 1 P)) -
        (D 0 0 (D 0 0 P + D 1 1 P) + D 1 1 (D 0 0 P + D 1 1 P)) := by
    rw [D_sub, D_sub, D_add, D_add]; ring
  have hs : D 0 0 P + D 1 1 P = C (a - b) * P := by
    simp only [D, map_sub]; linear_combination hZ - hW
  rw [Cas, h00, hs, D_C_mul, D_C_mul]
  simp only [casValue, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, Lap, N]
  simp only [map_sub, map_one] at hZ0 hZ1 hW0 hW1 hs
  linear_combination 2 * e00 + 2 * e11 + 2 * e01 + 2 * e10 + 4 * hZ +
    2 * z 0 * hZ0 + 2 * z 1 * hZ1 + 2 * (C a - 1) * hZ + 4 * hW + 2 * w 0 * hW0 +
    2 * w 1 * hW1 + 2 * (C b - 1) * hW - (C a - C b) * hs

/-! ## The Laplacian -/

theorem Lap_add (P Q : Pol) : Lap (P + Q) = Lap P + Lap Q := by
  simp [Lap, dz_add, dw_add]; ring

theorem Lap_sub (P Q : Pol) : Lap (P - Q) = Lap P - Lap Q := by
  simp [Lap, dz_sub, dw_sub]; ring

theorem Lap_C_mul (c : ℂ) (P : Pol) : Lap (C c * P) = C c * Lap P := by
  simp [Lap, dz_C_mul, dw_C_mul]; ring

theorem Lap_z_mul (i : Fin 2) (Y : Pol) : Lap (z i * Y) = dw i Y + z i * Lap Y := by
  fin_cases i <;> simp [Lap, dz_mul, dw_mul, dz_z, dw_z] <;> ring

theorem Lap_w_mul (k : Fin 2) (Y : Pol) : Lap (w k * Y) = dz k Y + w k * Lap Y := by
  fin_cases k <;> simp [Lap, dz_mul, dw_mul, dz_w, dw_w, dz_add] <;> ring

theorem Lap_dz (k : Fin 2) (Y : Pol) : Lap (dz k Y) = dz k (Lap Y) := by
  simp only [Lap, dz_add]
  rw [← dz_dw k 0, ← dz_dw k 1, dz_dz 0 k, dz_dz 1 k]

theorem Lap_dw (k : Fin 2) (Y : Pol) : Lap (dw k Y) = dw k (Lap Y) := by
  simp only [Lap, dw_add]
  rw [dw_dw 0 k, dz_dw 0 k, dw_dw 1 k, dz_dw 1 k, dz_dw 0 0, dz_dw 1 1]

theorem Lap_N_mul (Y : Pol) : Lap (N * Y) = 2 * Y + EZ Y + EW Y + N * Lap Y := by
  have e : N * Y = z 0 * (w 0 * Y) + z 1 * (w 1 * Y) := by unfold N; ring
  rw [e, Lap_add, Lap_z_mul, Lap_z_mul, Lap_w_mul, Lap_w_mul]
  simp only [EZ, EW, Lap, N, dw_mul, dw_w]
  simp
  ring

theorem Lap_N_mul_of_mem {a b : ℂ} {Y : Pol} (h : Y ∈ Eig a b) :
    Lap (N * Y) = C (2 + a + b) * Y + N * Lap Y := by
  rw [Lap_N_mul, h.1, h.2]
  simp only [map_add, map_ofNat]
  ring

/-- The polynomial of the holomorphic raising move `E^h_{ik}` at a level with exponent `s`:
`s z_i w_k h + N z_i ∂_{z_k} h`. -/
def holMove (s : ℂ) (i k : Fin 2) (h : Pol) : Pol :=
  C s * (z i * (w k * h)) + N * (z i * dz k h)

theorem holMove_mem {a b : ℂ} {h : Pol} (hh : h ∈ Eig a b) (s : ℂ) (i k : Fin 2) :
    holMove s i k h ∈ Eig (a + 1) (b + 1) := by
  have h1 : z i * (w k * h) ∈ Eig (a + 1) (b + 1) := z_mul_mem (w_mul_mem hh k) i
  have h2 : z i * dz k h ∈ Eig a b := by
    have := z_mul_mem (dz_mem hh k) i
    rwa [sub_add_cancel] at this
  have h3 := N_mul_mem h2
  rw [holMove, ← smul_eq_C_mul]
  exact add_mem (Submodule.smul_mem _ _ h1) h3

/-- For a harmonic `h ∈ Eig a b`, `Δ² (s z_i w_k h + N z_i ∂_k h) = 2(s+a+b+1) ∂_k ∂̄_i h`. -/
theorem Lap_Lap_holMove {a b : ℂ} {h : Pol} (hh : h ∈ Eig a b) (hΔ : Lap h = 0) (s : ℂ)
    (i k : Fin 2) :
    Lap (Lap (holMove s i k h)) = C (2 * (s + a + b + 1)) * dz k (dw i h) := by
  have hY : z i * dz k h ∈ Eig a b := by
    have := z_mul_mem (dz_mem hh k) i
    rwa [sub_add_cancel] at this
  have hG : dz k (dw i h) ∈ Eig (a - 1) (b - 1) := dz_mem (dw_mem hh i) k
  have hLG : Lap (dz k (dw i h)) = 0 := by rw [Lap_dz, Lap_dw, hΔ, dw_zero, dz_zero]
  have hLY : Lap (z i * dz k h) = dz k (dw i h) := by
    rw [Lap_z_mul, Lap_dz, hΔ, dz_zero, mul_zero, add_zero, dz_dw]
  have h1 : Lap (z i * (w k * h)) = dw i (w k * h) + z i * dz k h := by
    rw [Lap_z_mul, Lap_w_mul, hΔ, mul_zero, add_zero]
  have h2 : Lap (dw i (w k * h)) = dz k (dw i h) := by
    rw [Lap_dw, Lap_w_mul, hΔ, mul_zero, add_zero, dz_dw]
  rw [holMove, Lap_add, Lap_C_mul, Lap_N_mul_of_mem hY, hLY, Lap_add, Lap_C_mul, Lap_add,
    Lap_C_mul, h1, Lap_add, h2, hLY, Lap_N_mul_of_mem hG, hLG]
  simp only [map_add, map_mul, map_sub, map_ofNat, map_one]
  ring

/-! ## Coefficients and the eigenspaces -/

/-- The degree in `z` of an exponent vector. -/
def degZ (d : Var →₀ ℕ) : ℕ := d (Sum.inl 0) + d (Sum.inl 1)

/-- The degree in `w` of an exponent vector. -/
def degW (d : Var →₀ ℕ) : ℕ := d (Sum.inr 0) + d (Sum.inr 1)

theorem EZ_monomial (u : Var →₀ ℕ) (c : ℂ) :
    EZ (monomial u c) = monomial u ((degZ u : ℂ) * c) := by
  simp only [EZ, dz, z, X_mul_pderiv_monomial, degZ]
  rw [← add_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_monomial, smul_eq_mul]

theorem coeff_EZ (P : Pol) (d : Var →₀ ℕ) : (EZ P).coeff d = (degZ d : ℂ) * P.coeff d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [EZ, dz_add, mul_add] at hp hq ⊢
    simp at hp hq ⊢
    linear_combination hp + hq
  | monomial u c =>
    rw [EZ_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp

theorem EW_monomial (u : Var →₀ ℕ) (c : ℂ) :
    EW (monomial u c) = monomial u ((degW u : ℂ) * c) := by
  simp only [EW, dw, w, X_mul_pderiv_monomial, degW]
  rw [← add_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_monomial, smul_eq_mul]

theorem coeff_EW (P : Pol) (d : Var →₀ ℕ) : (EW P).coeff d = (degW d : ℂ) * P.coeff d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [EW, dw_add, mul_add] at hp hq ⊢
    simp at hp hq ⊢
    linear_combination hp + hq
  | monomial u c =>
    rw [EW_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp

theorem mem_Eig_iff_coeff {a b : ℂ} {P : Pol} :
    P ∈ Eig a b ↔ ∀ d, P.coeff d ≠ 0 → (degZ d : ℂ) = a ∧ (degW d : ℂ) = b := by
  constructor
  · rintro ⟨h1, h2⟩ d hd
    have e1 := congrArg (fun Q : Pol => Q.coeff d) h1
    have e2 := congrArg (fun Q : Pol => Q.coeff d) h2
    simp only [coeff_EZ, coeff_C_mul] at e1
    simp only [coeff_EW, coeff_C_mul] at e2
    exact ⟨mul_right_cancel₀ hd e1, mul_right_cancel₀ hd e2⟩
  · intro h
    refine ⟨MvPolynomial.ext _ _ fun d => ?_, MvPolynomial.ext _ _ fun d => ?_⟩
    · rw [coeff_EZ, coeff_C_mul]
      by_cases hd : P.coeff d = 0
      · rw [hd]; ring
      · rw [(h d hd).1]
    · rw [coeff_EW, coeff_C_mul]
      by_cases hd : P.coeff d = 0
      · rw [hd]; ring
      · rw [(h d hd).2]

theorem Eig_eq_bot_left {a b : ℂ} (ha : ∀ n : ℕ, (n : ℂ) ≠ a) : Eig a b = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [Submodule.mem_bot]
  ext d
  by_contra hd
  exact ha _ ((mem_Eig_iff_coeff.mp hP d hd).1)

theorem Eig_eq_bot_right {a b : ℂ} (hb : ∀ n : ℕ, (n : ℂ) ≠ b) : Eig a b = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [Submodule.mem_bot]
  ext d
  by_contra hd
  exact hb _ ((mem_Eig_iff_coeff.mp hP d hd).2)

theorem natCast_ne_neg_one (n : ℕ) : (n : ℂ) ≠ -1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem dw_eq_zero_of_mem {a : ℂ} {P : Pol} (h : P ∈ Eig a 0) (k : Fin 2) : dw k P = 0 := by
  have := dw_mem h k
  rw [zero_sub, Eig_eq_bot_right natCast_ne_neg_one] at this
  exact this

theorem dz_eq_zero_of_mem {b : ℂ} {P : Pol} (h : P ∈ Eig 0 b) (k : Fin 2) : dz k P = 0 := by
  have := dz_mem h k
  rw [zero_sub, Eig_eq_bot_left natCast_ne_neg_one] at this
  exact this

theorem Lap_eq_zero_of_mem_left {a : ℂ} {P : Pol} (h : P ∈ Eig a 0) : Lap P = 0 := by
  simp [Lap, dw_eq_zero_of_mem h, dz_zero]

theorem Lap_eq_zero_of_mem_right {b : ℂ} {P : Pol} (h : P ∈ Eig 0 b) : Lap P = 0 := by
  simp only [Lap, dz_dw, dz_eq_zero_of_mem h, dw_zero, add_zero]

/-! ## Nonvanishing of second derivatives -/

theorem exists_dz_dw_ne_zero {a b : ℂ} {h : Pol} (hh : h ∈ Eig a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : h ≠ 0) : ∃ i k : Fin 2, dz k (dw i h) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hdz : ∀ k, dz k h = 0 := by
    intro k
    have e := (dz_mem hh k).2
    simp only [EW, ← dz_dw, hall, mul_zero, add_zero] at e
    have hCb : (C b : Pol) ≠ 0 := by simpa using hb
    exact (mul_eq_zero.mp e.symm).resolve_left hCb
  have e := hh.1
  simp only [EZ, hdz, mul_zero, add_zero] at e
  have hCa : (C a : Pol) ≠ 0 := by simpa using ha
  exact h0 ((mul_eq_zero.mp e.symm).resolve_left hCa)

/-- The three second derivatives produced by the traceless holomorphic moves do not all vanish
on a nonzero harmonic polynomial of positive bidegree. -/
theorem exists_traceless_ne_zero {a b : ℂ} {h : Pol} (hh : h ∈ Eig a b) (hΔ : Lap h = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (h0 : h ≠ 0) :
    dz 1 (dw 0 h) ≠ 0 ∨ dz 0 (dw 1 h) ≠ 0 ∨ dz 0 (dw 0 h) - dz 1 (dw 1 h) ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨h10, h01, hd⟩ := hall
  have hsum : dz 0 (dw 0 h) + dz 1 (dw 1 h) = 0 := hΔ
  have h00 : dz 0 (dw 0 h) = 0 := by
    have : (2 : Pol) * dz 0 (dw 0 h) = 0 := by linear_combination hsum + hd
    have h2 : (2 : Pol) ≠ 0 := by
      rw [← map_ofNat C 2, Ne, MvPolynomial.C_eq_zero]; norm_num
    exact (mul_eq_zero.mp this).resolve_left h2
  have h11 : dz 1 (dw 1 h) = 0 := by linear_combination hsum - h00
  obtain ⟨i, k, hik⟩ := exists_dz_dw_ne_zero hh ha hb h0
  fin_cases i <;> fin_cases k
  · exact hik h00
  · exact hik h10
  · exact hik h01
  · exact hik h11

/-! ## Spanning by products `z_k w_i R` -/

theorem natCast_add_one_eq {a : ℕ} {n : ℕ} (h : (n : ℂ) = (a : ℂ) + 1) : n = a + 1 := by
  exact_mod_cast h

/-- Every polynomial of bidegree `(a+1, b+1)` is a combination of products `z_k w_i R` with `R`
of bidegree `(a, b)`. -/
theorem mem_span_zw {a b : ℕ} {P : Pol} (hP : P ∈ Eig ((a : ℂ) + 1) ((b : ℂ) + 1)) :
    P ∈ Submodule.span ℂ
      {Q | ∃ (i k : Fin 2) (R : Pol), R ∈ Eig (a : ℂ) (b : ℂ) ∧ Q = z k * (w i * R)} := by
  classical
  rw [as_sum P]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hc := mem_Eig_iff_coeff.mp hP d (mem_support_iff.mp hd)
  have hz : degZ d = a + 1 := natCast_add_one_eq hc.1
  have hw : degW d = b + 1 := natCast_add_one_eq hc.2
  have hk : ∃ k : Fin 2, d (Sum.inl k) ≠ 0 := by
    by_contra hne
    push Not at hne
    simp [degZ, hne 0, hne 1] at hz
  have hi : ∃ i : Fin 2, d (Sum.inr i) ≠ 0 := by
    by_contra hne
    push Not at hne
    simp [degW, hne 0, hne 1] at hw
  obtain ⟨k, hk⟩ := hk
  obtain ⟨i, hi⟩ := hi
  set e : Var →₀ ℕ := d - Finsupp.single (Sum.inl k) 1 - Finsupp.single (Sum.inr i) 1 with he
  have hde : d = Finsupp.single (Sum.inl k) 1 + (Finsupp.single (Sum.inr i) 1 + e) := by
    ext v
    rcases v with v | v
    · simp only [he, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false]
      split_ifs with h
      · subst h; omega
      · omega
    · simp only [he, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false]
      split_ifs with h
      · subst h; omega
      · omega
  refine Submodule.subset_span ⟨i, k, monomial e (P.coeff d), ?_, ?_⟩
  · rw [mem_Eig_iff_coeff]
    intro d' hd'
    rw [coeff_monomial] at hd'
    split_ifs at hd' with h
    · subst h
      have e1 : degZ d = degZ e + 1 := by
        rw [hde]; simp [degZ, Finsupp.single_apply]
        fin_cases k <;> simp <;> ring
      have e2 : degW d = degW e + 1 := by
        rw [hde]; simp [degW, Finsupp.single_apply]
        fin_cases i <;> simp <;> ring
      constructor
      · exact_mod_cast (by omega : degZ e = a)
      · exact_mod_cast (by omega : degW e = b)
    · exact absurd rfl hd'
  · rw [z, w, X, X, monomial_mul_monomial, monomial_mul_monomial, ← hde, one_mul, one_mul]

/-! ## Injectivity of evaluation at `(r, r̄)` -/

/-- Evaluation of a polynomial at `(r, r̄)`. -/
def ev (r : Fin 2 → ℂ) (P : Pol) : ℂ :=
  eval (Sum.elim r fun k => starRingEnd ℂ (r k)) P

/-- The substitution `z_k ↦ x_k + i y_k`, `w_k ↦ x_k - i y_k` (with `x_k = X (inl k)`,
`y_k = X (inr k)`). -/
def toReal : Pol →ₐ[ℂ] Pol :=
  bind₁ (Sum.elim (fun k => X (Sum.inl k) + C Complex.I * X (Sum.inr k))
    fun k => X (Sum.inl k) - C Complex.I * X (Sum.inr k))

/-- The inverse substitution `x_k ↦ (z_k + w_k)/2`, `y_k ↦ (z_k - w_k)/(2i)`. -/
def fromReal : Pol →ₐ[ℂ] Pol :=
  bind₁ (Sum.elim (fun k => C (1 / 2) * (X (Sum.inl k) + X (Sum.inr k)))
    fun k => C (-Complex.I / 2) * (X (Sum.inl k) - X (Sum.inr k)))

theorem fromReal_toReal (P : Pol) : fromReal (toReal P) = P := by
  have h : fromReal.comp toReal = AlgHom.id ℂ Pol := by
    apply MvPolynomial.algHom_ext
    have h1 : (C Complex.I : Pol) * C (-Complex.I / 2) = C (1 / 2) := by
      rw [← map_mul]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    have h2 : (C (1 / 2) : Pol) * 2 = 1 := by
      rw [← map_ofNat C 2, ← map_mul]; norm_num
    intro v
    rcases v with k | k
    · simp only [fromReal, toReal, AlgHom.coe_comp, Function.comp_apply, bind₁_X_right,
        Sum.elim_inl, map_add, map_mul, bind₁_C_right, Sum.elim_inr, AlgHom.coe_id, id_eq]
      linear_combination (X (Sum.inl k) - X (Sum.inr k)) * h1 + X (Sum.inl k) * h2
    · simp only [fromReal, toReal, AlgHom.coe_comp, Function.comp_apply, bind₁_X_right,
        Sum.elim_inr, map_sub, map_mul, bind₁_C_right, Sum.elim_inl, AlgHom.coe_id, id_eq]
      linear_combination -(X (Sum.inl k) - X (Sum.inr k)) * h1 + X (Sum.inr k) * h2
  exact congrArg (fun φ : Pol →ₐ[ℂ] Pol => φ P) h

/-- A polynomial in `r, r̄` vanishing at every `(r, r̄)` with `r ≠ 0` is zero. -/
theorem eq_zero_of_ev (P : Pol) (h : ∀ r : Fin 2 → ℂ, r ≠ 0 → ev r P = 0) : P = 0 := by
  have h0 : toReal P = 0 := by
    have hs : ∀ v : Var, (Set.range ((↑) : ℝ → ℂ) \ {0}).Infinite := fun _ =>
      (Set.infinite_range_of_injective Complex.ofReal_injective).diff (Set.finite_singleton 0)
    refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ) \ {0}) hs fun x hx => ?_
    rw [map_zero]
    have hre : ∀ v, starRingEnd ℂ (x v) = x v := by
      intro v
      obtain ⟨⟨y, hy⟩, -⟩ := hx v trivial
      rw [← hy, Complex.conj_ofReal]
    have key : (fun v : Var => eval x ((Sum.elim (fun k => X (Sum.inl k) + C Complex.I *
        X (Sum.inr k)) fun k => X (Sum.inl k) - C Complex.I * X (Sum.inr k) : Var → Pol) v)) =
        Sum.elim (fun k => x (Sum.inl k) + Complex.I * x (Sum.inr k))
          fun k => starRingEnd ℂ (x (Sum.inl k) + Complex.I * x (Sum.inr k)) := by
      funext v
      rcases v with k | k
      · simp
      · simp [hre, Complex.conj_I]; ring
    have hr0 : (fun k => x (Sum.inl k) + Complex.I * x (Sum.inr k)) ≠ 0 := by
      intro hzero
      have h1 := congrArg (fun r : Fin 2 → ℂ => (r 0).re) hzero
      obtain ⟨⟨y0, hy0⟩, hne0⟩ := hx (Sum.inl 0) trivial
      obtain ⟨⟨y1, hy1⟩, -⟩ := hx (Sum.inr 0) trivial
      simp only [Pi.zero_apply, Complex.zero_re, Complex.add_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, zero_sub] at h1
      rw [← hy0, ← hy1] at h1
      simp at h1
      apply hne0
      rw [← hy0, h1]
      simp
    have := h _ hr0
    rw [ev, ← key] at this
    change aeval x (toReal P) = 0
    rw [toReal, aeval_bind₁]
    exact this
  rw [← fromReal_toReal P, h0, map_zero]

/-! ## Irreducibility of the bottom `U(2)`-type

Polynomials in two variables `X u`, `X v` of degree `m` (the spaces `Eig m 0` and `Eig 0 m`)
form an irreducible module for the raising and lowering operators `X u ∂_v`, `X v ∂_u`. -/

section TwoVar

variable (u v : Var) (m : ℕ)

/-- The monomial `X u ^ (m - t) * X v ^ t`. -/
def mono (t : ℕ) : Pol := X u ^ (m - t) * X v ^ t

/-- Its exponent vector. -/
def dmono (t : ℕ) : Var →₀ ℕ := Finsupp.single u (m - t) + Finsupp.single v t

theorem mono_eq_monomial (t : ℕ) : mono u v m t = monomial (dmono u v m t) 1 := by
  rw [mono, dmono, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- Polynomials supported on the monomials `X u ^ (m - t) * X v ^ t`, `t ≤ m`. -/
def Two : Submodule ℂ Pol where
  carrier := {P | ∀ d, P.coeff d ≠ 0 → ∃ t ≤ m, d = dmono u v m t}
  zero_mem' d hd := by simp at hd
  add_mem' {P Q} hP hQ d hd := by
    by_cases h : P.coeff d = 0
    · refine hQ d fun hq => hd ?_
      simp [h, hq]
    · exact hP d h
  smul_mem' c P hP d hd := hP d fun h => hd (by simp [h])

/-- The raising operator `X u ∂_v`. -/
def raise : Pol →ₗ[ℂ] Pol := LinearMap.mulLeft ℂ (X u) ∘ₗ (pderiv v).toLinearMap

theorem raise_apply (P : Pol) : raise u v P = X u * pderiv v P := rfl

variable {u v}

theorem dmono_apply_right (huv : u ≠ v) (t : ℕ) : dmono u v m t v = t := by
  simp [dmono, Finsupp.single_apply, huv]

theorem dmono_injOn (huv : u ≠ v) {t t' : ℕ} (h : dmono u v m t = dmono u v m t') : t = t' := by
  have := congrArg (fun d => d v) h
  simpa [dmono_apply_right m huv] using this

theorem Two_repr (huv : u ≠ v) {P : Pol} (hP : P ∈ Two u v m) :
    P = ∑ t ∈ Finset.range (m + 1), C (P.coeff (dmono u v m t)) * mono u v m t := by
  classical
  ext d
  simp only [mono_eq_monomial, coeff_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one,
    mul_zero]
  by_cases hd : P.coeff d = 0
  · rw [hd, eq_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    split_ifs with h
    · rw [h, hd]
    · rfl
  · obtain ⟨t, ht, rfl⟩ := hP d hd
    rw [Finset.sum_eq_single t]
    · simp
    · intro t' _ ht'
      rw [if_neg]
      exact fun h => ht' (dmono_injOn m huv h)
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le ht)) h

theorem raise_mono (huv : u ≠ v) (t : ℕ) (ht : t ≤ m) :
    raise u v (mono u v m t) = C (t : ℂ) * mono u v m (t - 1) := by
  rw [raise_apply, mono, pderiv_mul, pderiv_pow, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne huv]
  rcases t with _ | t
  · simp
  · rw [mono, show m - (t + 1 - 1) = m - (t + 1) + 1 by omega, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, mul_zero, zero_mul, zero_add, mul_one,
      add_tsub_cancel_right, map_add, map_one, map_natCast]
    ring

theorem raise_pow_mono (huv : u ≠ v) (j t : ℕ) (ht : t ≤ m) :
    (raise u v ^ j) (mono u v m t) = C (t.descFactorial j : ℂ) * mono u v m (t - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_mul_eq_C_mul, raise_mono m huv _ (by omega),
      Nat.descFactorial_succ, ← mul_assoc, ← map_mul, Nat.sub_sub]
    push_cast
    ring_nf
  where
    map_mul_eq_C_mul : ∀ (c : ℂ) (Q : Pol), raise u v (C c * Q) = C c * raise u v Q := by
      intro c Q
      rw [raise_apply, raise_apply, pderiv_C_mul]
      ring

variable (u v) in
/-- The lowering operator `X v ∂_u`. -/
def lower : Pol →ₗ[ℂ] Pol := LinearMap.mulLeft ℂ (X v) ∘ₗ (pderiv u).toLinearMap

theorem lower_apply (P : Pol) : lower u v P = X v * pderiv u P := rfl

theorem lower_mono (huv : u ≠ v) (t : ℕ) :
    lower u v (mono u v m t) = C ((m - t : ℕ) : ℂ) * mono u v m (t + 1) := by
  rw [lower_apply, mono, mono, pderiv_mul, pderiv_pow, pderiv_pow, pderiv_X_self,
    pderiv_X_of_ne huv.symm, show m - (t + 1) = m - t - 1 by omega, pow_succ (X v) t,
    map_natCast]
  ring

theorem lower_pow_mono (huv : u ≠ v) (j t : ℕ) :
    (lower u v ^ j) (mono u v m t) =
      C ((m - t).descFactorial j : ℂ) * mono u v m (t + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, ← smul_eq_C_mul, LinearMap.map_smul,
      lower_mono m huv, Nat.descFactorial_succ, smul_eq_C_mul, ← mul_assoc, ← map_mul,
      Nat.sub_sub, ← add_assoc]
    push_cast
    ring_nf

theorem Two_repr' (huv : u ≠ v) {P : Pol} (hP : P ∈ Two u v m) :
    P = ∑ t ∈ Finset.range (m + 1), P.coeff (dmono u v m t) • mono u v m t := by
  conv_lhs => rw [Two_repr m huv hP]
  simp only [smul_eq_C_mul]

theorem pow_mem_of_mem (f : Pol →ₗ[ℂ] Pol) (V : Submodule ℂ Pol) (hf : ∀ P ∈ V, f P ∈ V)
    (j : ℕ) {P : Pol} (hP : P ∈ V) : (f ^ j) P ∈ V := by
  induction j with
  | zero => simpa using hP
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hf _ ih

/-- A nonzero subspace of `Two u v m` stable under raising and lowering is everything. -/
theorem Two_le (huv : u ≠ v) (V : Submodule ℂ Pol) (hV : V ≤ Two u v m) (h0 : V ≠ ⊥)
    (hR : ∀ P ∈ V, raise u v P ∈ V) (hL : ∀ P ∈ V, lower u v P ∈ V) : Two u v m ≤ V := by
  classical
  obtain ⟨P, hPV, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hrep := Two_repr' m huv (hV hPV)
  set c : ℕ → ℂ := fun t => P.coeff (dmono u v m t) with hc
  have hT : ((Finset.range (m + 1)).filter fun t => c t ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hP0
    rw [hrep]
    refine Finset.sum_eq_zero fun t ht => ?_
    have := h ht
    rw [not_not] at this
    change c t • _ = 0
    rw [this, zero_smul]
  set τ := ((Finset.range (m + 1)).filter fun t => c t ≠ 0).max' hT with hτ
  have hτmem := Finset.max'_mem _ hT
  rw [← hτ, Finset.mem_filter, Finset.mem_range] at hτmem
  have key : (raise u v ^ τ) P = (c τ * (τ.factorial : ℂ)) • mono u v m 0 := by
    rw [hrep, map_sum, Finset.sum_eq_single τ]
    · rw [LinearMap.map_smul, raise_pow_mono m huv _ _ (by omega), Nat.descFactorial_self,
        Nat.sub_self, smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul]
    · intro t ht htτ
      by_cases hct : c t = 0
      · change (raise u v ^ τ) (c t • _) = 0
        rw [hct, zero_smul, map_zero]
      · have hle : t ≤ τ := Finset.le_max' _ t (by
          rw [Finset.mem_filter]; exact ⟨ht, hct⟩)
        have hlt : t < τ := lt_of_le_of_ne hle htτ
        rw [LinearMap.map_smul, raise_pow_mono m huv _ _ (by
          rw [Finset.mem_range] at ht; omega), (Nat.descFactorial_eq_zero_iff_lt).mpr hlt]
        simp
    · intro h
      exact absurd (Finset.mem_range.mpr hτmem.1) h
  have hne : c τ * (τ.factorial : ℂ) ≠ 0 :=
    mul_ne_zero hτmem.2 (by exact_mod_cast (Nat.factorial_pos τ).ne')
  have hm0 : mono u v m 0 ∈ V := by
    have h1 := pow_mem_of_mem _ V hR τ hPV
    rw [key] at h1
    have := V.smul_mem (c τ * (τ.factorial : ℂ))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hmt : ∀ t ≤ m, mono u v m t ∈ V := by
    intro t ht
    have h1 := pow_mem_of_mem _ V hL t hm0
    rw [lower_pow_mono m huv, Nat.sub_zero, zero_add, ← smul_eq_C_mul] at h1
    have hd : (m.descFactorial t : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr ht).ne' -- placeholder
    have := V.smul_mem (m.descFactorial t : ℂ)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at this
  intro Q hQ
  rw [Two_repr' m huv hQ]
  exact Submodule.sum_mem _ fun t ht =>
    V.smul_mem _ (hmt t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))

end TwoVar

theorem Eig_le_Two_left (m : ℕ) : Eig (m : ℂ) 0 ≤ Two (Sum.inl 0) (Sum.inl 1) m := by
  intro P hP d hd
  obtain ⟨h1, h2⟩ := mem_Eig_iff_coeff.mp hP d hd
  have hz : degZ d = m := by exact_mod_cast h1
  have hw : degW d = 0 := by exact_mod_cast h2
  simp only [degZ, degW] at hz hw
  refine ⟨d (Sum.inl 1), by omega, ?_⟩
  ext v
  rcases v with k | k <;> fin_cases k <;> simp [dmono, Finsupp.single_apply] <;> omega

theorem Eig_le_Two_right (m : ℕ) : Eig 0 (m : ℂ) ≤ Two (Sum.inr 1) (Sum.inr 0) m := by
  intro P hP d hd
  obtain ⟨h1, h2⟩ := mem_Eig_iff_coeff.mp hP d hd
  have hz : degZ d = 0 := by exact_mod_cast h1
  have hw : degW d = m := by exact_mod_cast h2
  simp only [degZ, degW] at hz hw
  refine ⟨d (Sum.inr 0), by omega, ?_⟩
  ext v
  rcases v with k | k <;> fin_cases k <;> simp [dmono, Finsupp.single_apply] <;> omega

/-- The bottom type `Eig m 0` is irreducible under `D 0 1` and `D 1 0`. -/
theorem Eig_le_of_stable_left (m : ℕ) (V : Submodule ℂ Pol) (hV : V ≤ Eig (m : ℂ) 0)
    (h0 : V ≠ ⊥) (h01 : ∀ P ∈ V, D 0 1 P ∈ V) (h10 : ∀ P ∈ V, D 1 0 P ∈ V) :
    Eig (m : ℂ) 0 ≤ V := by
  have huv : (Sum.inl 0 : Var) ≠ Sum.inl 1 := by simp
  refine (Eig_le_Two_left m).trans (Two_le m huv V ((hV.trans (Eig_le_Two_left m))) h0 ?_ ?_)
  · intro P hP
    have e : raise (Sum.inl 0) (Sum.inl 1) P = D 0 1 P := by
      rw [raise_apply, D, dw_eq_zero_of_mem (hV hP), mul_zero, sub_zero]; rfl
    rw [e]; exact h01 P hP
  · intro P hP
    have e : lower (Sum.inl 0) (Sum.inl 1) P = D 1 0 P := by
      rw [lower_apply, D, dw_eq_zero_of_mem (hV hP), mul_zero, sub_zero]; rfl
    rw [e]; exact h10 P hP

/-- The bottom type `Eig 0 m` is irreducible under `D 0 1` and `D 1 0`. -/
theorem Eig_le_of_stable_right (m : ℕ) (V : Submodule ℂ Pol) (hV : V ≤ Eig 0 (m : ℂ))
    (h0 : V ≠ ⊥) (h01 : ∀ P ∈ V, D 0 1 P ∈ V) (h10 : ∀ P ∈ V, D 1 0 P ∈ V) :
    Eig 0 (m : ℂ) ≤ V := by
  have huv : (Sum.inr 1 : Var) ≠ Sum.inr 0 := by simp
  refine (Eig_le_Two_right m).trans (Two_le m huv V ((hV.trans (Eig_le_Two_right m))) h0 ?_ ?_)
  · intro P hP
    have e : raise (Sum.inr 1) (Sum.inr 0) P = -D 0 1 P := by
      rw [raise_apply, D, dz_eq_zero_of_mem (hV hP), mul_zero, zero_sub, neg_neg]; rfl
    rw [e]; exact V.neg_mem (h01 P hP)
  · intro P hP
    have e : lower (Sum.inr 1) (Sum.inr 0) P = -D 1 0 P := by
      rw [lower_apply, D, dz_eq_zero_of_mem (hV hP), mul_zero, zero_sub, neg_neg]; rfl
    rw [e]; exact V.neg_mem (h10 P hP)

end Langlands.Archimedean.GLTwoPoly
