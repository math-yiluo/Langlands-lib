import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The small integral representations of `SL₂`

For `m ≤ 3`, `gam m g` is the matrix of a `2 × 2` matrix `g` acting on the divided-power module
`Γ^m(R²)` in the basis `x^[r] y^[m-r]` (`r = 0, …, m`), where `g x = g₀₀ x + g₁₀ y` and
`g y = g₀₁ x + g₁₁ y`. The assignment is multiplicative on all `2 × 2` matrices.

`cart i₀ c g` is the matrix of `g` on the lattice `ℤ v₋ ⊕ ℤ v₊ ⊕ ℤ^ι` spanned by the two root
vectors `v₋ = y^[2]`, `v₊ = x^[2]` of a root `α` and the Cartan vectors `u_t` of the adjoint
representation, where `u_{i₀}` plays the role of `xy` and `e u_t = c_t v₊`, `f u_t = c_t v₋`.
It is multiplicative on matrices of determinant one when `c i₀ = 2`.

The matrices `gamE`, `gamF`, `cartE`, `cartF` are the integral divided powers of the raising and
lowering operators; they give the values at the unipotent matrices.
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {R : Type*} [CommRing R]

/-- The matrix of `g` on `Γ^m(R²)` in the basis `x^[r] y^[m-r]`, for `m ≤ 3`, and the identity
for `m ≥ 4`. -/
def gam : (m : ℕ) → Matrix (Fin 2) (Fin 2) R → Matrix (Fin (m + 1)) (Fin (m + 1)) R
  | 0, _ => 1
  | 1, g => !![g 1 1, g 1 0; g 0 1, g 0 0]
  | 2, g => !![g 1 1 ^ 2, 2 * g 1 0 * g 1 1, g 1 0 ^ 2;
      g 0 1 * g 1 1, g 0 0 * g 1 1 + g 0 1 * g 1 0, g 0 0 * g 1 0;
      g 0 1 ^ 2, 2 * g 0 0 * g 0 1, g 0 0 ^ 2]
  | 3, g => !![g 1 1 ^ 3, 3 * g 1 0 * g 1 1 ^ 2, 3 * g 1 0 ^ 2 * g 1 1, g 1 0 ^ 3;
      g 0 1 * g 1 1 ^ 2, g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1,
        2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2, g 0 0 * g 1 0 ^ 2;
      g 0 1 ^ 2 * g 1 1, 2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0,
        g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0, g 0 0 ^ 2 * g 1 0;
      g 0 1 ^ 3, 3 * g 0 0 * g 0 1 ^ 2, 3 * g 0 0 ^ 2 * g 0 1, g 0 0 ^ 3]
  | _ + 4, _ => 1

theorem gam_mul (m : ℕ) (g h : Matrix (Fin 2) (Fin 2) R) :
    gam m (g * h) = gam m g * gam m h := by
  rcases m with _ | _ | _ | _ | m
  · simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [gam, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [gam, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [gam, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  · simp [gam]

theorem gam_one (m : ℕ) : gam m (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rcases m with _ | _ | _ | _ | m
  · simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · simp [gam]

theorem gam_map {S : Type*} [CommRing S] (f : R →+* S) (m : ℕ) (g : Matrix (Fin 2) (Fin 2) R) :
    (gam m g).map f = gam m (g.map f) := by
  rcases m with _ | _ | _ | _ | m
  · simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, map_ofNat f 2]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, map_ofNat f 2, map_ofNat f 3]
  · simp [gam]

/-- The `k`-th divided power of the raising operator on `Γ^m`: it sends `x^[c] y^[m-c]` to
`C(c+k, k) x^[c+k] y^[m-c-k]`. -/
def gamE (m k : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  of fun r c => if (c : ℕ) + k = r then ((r : ℕ).choose k : ℤ) else 0

/-- The `k`-th divided power of the lowering operator on `Γ^m`: it sends `x^[c] y^[m-c]` to
`C(m-c+k, k) x^[c-k] y^[m-c+k]`. -/
def gamF (m k : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  of fun r c => if (r : ℕ) + k = c then ((m - r : ℕ).choose k : ℤ) else 0

theorem gamE_zero (m : ℕ) : gamE m 0 = 1 := by
  ext r c
  simp only [gamE, of_apply, add_zero, Nat.choose_zero_right, Nat.cast_one, one_apply]
  by_cases h : r = c
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.ext h'.symm)), ite_eq_right h]

theorem gamF_zero (m : ℕ) : gamF m 0 = 1 := by
  ext r c
  simp only [gamF, of_apply, add_zero, Nat.choose_zero_right, Nat.cast_one, one_apply]
  by_cases h : r = c
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h]

theorem gamE_eq_zero {m k : ℕ} (hk : m < k) : gamE m k = 0 := by
  ext r c
  simp only [gamE, of_apply, zero_apply]
  rw [ite_eq_right]
  omega

theorem gamF_eq_zero {m k : ℕ} (hk : m < k) : gamF m k = 0 := by
  ext r c
  simp only [gamF, of_apply, zero_apply]
  rw [ite_eq_right]
  omega

theorem gamE_mul (m a b : ℕ) :
    gamE m a * gamE m b = ((a + b).choose a : ℤ) • gamE m (a + b) := by
  ext r c
  simp only [gamE, mul_apply, of_apply, smul_apply, smul_eq_mul]
  by_cases h : (c : ℕ) + (a + b) = r
  · have hcb : (c : ℕ) + b < m + 1 := by omega
    rw [Fintype.sum_eq_single (⟨(c : ℕ) + b, hcb⟩ : Fin (m + 1))]
    · rw [ite_eq_left (show (c : ℕ) + b + a = r by omega), ite_eq_left rfl, ite_eq_left h]
      have key := Nat.choose_mul (n := (r : ℕ)) (k := a + b) (s := a) (by omega)
      rw [show (r : ℕ) - a = (c : ℕ) + b by omega, show a + b - a = b by omega] at key
      rw [mul_comm ((a + b).choose a : ℤ)]
      exact_mod_cast key.symm
    · intro t ht
      rw [ite_eq_right, zero_mul]
      intro hta
      exact ht (Fin.ext (by simp only; omega))
  · rw [ite_eq_right h, mul_zero]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h1 : (t : ℕ) + a = r
    · rw [ite_eq_left h1, ite_eq_right (by omega), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

theorem gamF_mul (m a b : ℕ) :
    gamF m a * gamF m b = ((a + b).choose a : ℤ) • gamF m (a + b) := by
  ext r c
  simp only [gamF, mul_apply, of_apply, smul_apply, smul_eq_mul]
  by_cases h : (r : ℕ) + (a + b) = c
  · have hra : (r : ℕ) + a < m + 1 := by omega
    rw [Fintype.sum_eq_single (⟨(r : ℕ) + a, hra⟩ : Fin (m + 1))]
    · rw [ite_eq_left rfl, ite_eq_left (show (r : ℕ) + a + b = c by omega), ite_eq_left h]
      have key := Nat.choose_mul (n := m - (r : ℕ)) (k := a + b) (s := a) (by omega)
      rw [show m - (r : ℕ) - a = m - ((r : ℕ) + a) by omega, show a + b - a = b by omega] at key
      rw [mul_comm ((a + b).choose a : ℤ)]
      exact_mod_cast key.symm
    · intro t ht
      rw [ite_eq_right, zero_mul]
      intro hta
      exact ht (Fin.ext (by simp only; omega))
  · rw [ite_eq_right h, mul_zero]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h1 : (r : ℕ) + a = t
    · rw [ite_eq_left h1, ite_eq_right (by omega), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

theorem sum_range_eq_of_eq_zero {M : Type*} [AddCommMonoid M] {f : ℕ → M} {a N N' : ℕ}
    (h : ∀ k, a ≤ k → f k = 0) (hN : a ≤ N) (hN' : a ≤ N') :
    ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range N', f k := by
  have key : ∀ M', a ≤ M' → ∑ k ∈ Finset.range a, f k = ∑ k ∈ Finset.range M', f k := by
    intro M' hM'
    apply Finset.sum_subset (Finset.range_subset_range.2 hM')
    intro k _ hk
    exact h k (by simpa using hk)
  rw [← key N hN, ← key N' hN']

theorem gam_upper_four {m : ℕ} (hm : m ≤ 3) (s : R) :
    gam m !![1, s; 0, 1] =
      ∑ k ∈ Finset.range 4, s ^ k • (gamE m k).map (Int.castRingHom R) := by
  interval_cases m
  · ext r c
    fin_cases r; fin_cases c
    simp [gam, gamE, Finset.sum_range_succ]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamE, Finset.sum_range_succ]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamE, Finset.sum_range_succ, Nat.choose] <;> ring
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamE, Finset.sum_range_succ, Nat.choose] <;> ring

theorem gam_lower_four {m : ℕ} (hm : m ≤ 3) (s : R) :
    gam m !![1, 0; s, 1] =
      ∑ k ∈ Finset.range 4, s ^ k • (gamF m k).map (Int.castRingHom R) := by
  interval_cases m
  · ext r c
    fin_cases r; fin_cases c
    simp [gam, gamF, Finset.sum_range_succ]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamF, Finset.sum_range_succ]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamF, Finset.sum_range_succ, Nat.choose] <;> ring
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam, gamF, Finset.sum_range_succ, Nat.choose] <;> ring

theorem gam_upper {m N : ℕ} (hm : m ≤ 3) (hN : m < N) (s : R) :
    gam m !![1, s; 0, 1] =
      ∑ k ∈ Finset.range N, s ^ k • (gamE m k).map (Int.castRingHom R) := by
  rw [gam_upper_four hm]
  refine sum_range_eq_of_eq_zero (a := m + 1) (fun k hk => ?_) (by omega) hN
  rw [gamE_eq_zero (by omega)]
  simp

theorem gam_lower {m N : ℕ} (hm : m ≤ 3) (hN : m < N) (s : R) :
    gam m !![1, 0; s, 1] =
      ∑ k ∈ Finset.range N, s ^ k • (gamF m k).map (Int.castRingHom R) := by
  rw [gam_lower_four hm]
  refine sum_range_eq_of_eq_zero (a := m + 1) (fun k hk => ?_) (by omega) hN
  rw [gamF_eq_zero (by omega)]
  simp

theorem gamE_ne_zero {m k : ℕ} {r c : Fin (m + 1)} (h : gamE m k r c ≠ 0) : (c : ℕ) + k = r := by
  by_contra h'
  exact h (by simp [gamE, h'])

theorem gamF_ne_zero {m k : ℕ} {r c : Fin (m + 1)} (h : gamF m k r c ≠ 0) : (r : ℕ) + k = c := by
  by_contra h'
  exact h (by simp [gamF, h'])

/-- The bracket of the raising and lowering operators on `Γ^m` is diagonal with entries
`2r - m`. -/
theorem gamE_one_mul_gamF_one_sub {m : ℕ} (hm : m ≤ 3) :
    gamE m 1 * gamF m 1 - gamF m 1 * gamE m 1 =
      diagonal fun r : Fin (m + 1) => 2 * (r : ℤ) - m := by
  interval_cases m <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [gamE, gamF, mul_apply, Fin.sum_univ_succ]

theorem gam_diag {m : ℕ} (hm : m ≤ 3) (t u : R) :
    gam m !![t, 0; 0, u] = diagonal fun r : Fin (m + 1) => t ^ (r : ℕ) * u ^ (m - r) := by
  interval_cases m
  · ext r c
    fin_cases r; fin_cases c
    simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp [gam] <;> ring

theorem gam_weyl_ne_zero {m : ℕ} (hm : m ≤ 3) {r c : Fin (m + 1)}
    (h : gam m (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) r c ≠ 0) :
    (r : ℕ) + c = m := by
  interval_cases m
  · fin_cases r; fin_cases c; rfl
  · fin_cases r <;> fin_cases c <;> simp_all [gam]
  · fin_cases r <;> fin_cases c <;> simp_all [gam]
  · fin_cases r <;> fin_cases c <;> simp_all [gam]

/-! ### The Cartan block of the adjoint representation -/

section Cartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (c : ι → ℤ)

/-- The matrix of `g` on the Cartan block `ℤ v₋ ⊕ ℤ v₊ ⊕ ℤ^ι` of a root (index `0` is `v₋`,
index `1` is `v₊`): `v₊ ↦ a² v₊ + aγ u_{i₀} + γ² v₋`, `v₋ ↦ b² v₊ + bδ u_{i₀} + δ² v₋`,
`u_t ↦ u_t + c_t (ab v₊ + bγ u_{i₀} + γδ v₋)` for `g = [[a, b], [γ, δ]]`. -/
def cart (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) R :=
  fromBlocks !![g 1 1 ^ 2, g 1 0 ^ 2; g 0 1 ^ 2, g 0 0 ^ 2]
    (of ![fun t => (c t : R) * (g 1 0 * g 1 1), fun t => (c t : R) * (g 0 0 * g 0 1)])
    (of fun t => ![if t = i₀ then g 0 1 * g 1 1 else 0, if t = i₀ then g 0 0 * g 1 0 else 0])
    (of fun t' t => (if t' = t then 1 else 0) + if t' = i₀ then (c t : R) * (g 0 1 * g 1 0) else 0)

theorem cart_mul (hc : c i₀ = 2) {g h : Matrix (Fin 2) (Fin 2) R}
    (hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1) (hh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1) :
    cart i₀ c (g * h) = cart i₀ c g * cart i₀ c h := by
  have hc' : (c i₀ : R) = 2 := by rw [hc]; norm_num
  simp only [cart, fromBlocks_multiply]
  congr 1
  · ext r r'
    simp only [Matrix.add_apply, Matrix.mul_apply]
    fin_cases r <;> fin_cases r' <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_ite_eq', hc'] <;> ring
  · ext r t
    simp only [Matrix.add_apply, Matrix.mul_apply]
    fin_cases r
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, hc']
      linear_combination (↑(c t) * (g 1 0 * g 1 1)) * hh
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, hc']
      linear_combination (↑(c t) * (g 0 0 * g 0 1)) * hh
  · ext t r
    simp only [Matrix.add_apply, Matrix.mul_apply]
    by_cases ht : t = i₀
    · subst ht
      fin_cases r
      · simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, hc']
        linear_combination (h 0 1 * h 1 1) * hg
      · simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, hc']
        linear_combination (h 0 0 * h 1 0) * hg
    · fin_cases r <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, ht]
  · ext t' t
    simp only [Matrix.add_apply, Matrix.mul_apply]
    by_cases ht : t' = i₀
    · subst ht
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, hc']
      split_ifs <;>
        linear_combination (↑(c t) * (h 0 1 * h 1 0)) * hg + (↑(c t) * (g 0 1 * g 1 0)) * hh
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq, mul_add, add_mul, ite_mul, mul_ite, ht]

theorem cart_one : cart i₀ c (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cart]
  · fin_cases r <;> simp [cart]
  · fin_cases r' <;> simp [cart]
  · simp [cart, one_apply]

theorem cart_map {S : Type*} [CommRing S] (f : R →+* S) (g : Matrix (Fin 2) (Fin 2) R) :
    (cart i₀ c g).map f = cart i₀ c (g.map f) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cart]
  · fin_cases r <;> simp [cart]
  · fin_cases r' <;> simp [cart, apply_ite f]
  · simp [cart, apply_ite f]

/-- The divided powers of the raising operator on the Cartan block: `e v₋ = u_{i₀}`,
`e u_t = c_t v₊`, `e v₊ = 0`, and `e^[2] v₋ = v₊`. -/
def cartE : ℕ → Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℤ
  | 0 => 1
  | 1 => fromBlocks 0 (of ![0, c]) (of fun t => ![if t = i₀ then 1 else 0, 0]) 0
  | 2 => fromBlocks !![0, 0; 1, 0] 0 0 0
  | _ + 3 => 0

/-- The divided powers of the lowering operator on the Cartan block: `f v₊ = u_{i₀}`,
`f u_t = c_t v₋`, `f v₋ = 0`, and `f^[2] v₊ = v₋`. -/
def cartF : ℕ → Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℤ
  | 0 => 1
  | 1 => fromBlocks 0 (of ![c, 0]) (of fun t => ![0, if t = i₀ then 1 else 0]) 0
  | 2 => fromBlocks !![0, 1; 0, 0] 0 0 0
  | _ + 3 => 0

theorem cartE_zero : cartE i₀ c 0 = 1 := rfl

theorem cartF_zero : cartF i₀ c 0 = 1 := rfl

theorem cartE_eq_zero {k : ℕ} (hk : 2 < k) : cartE i₀ c k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  rfl

theorem cartF_eq_zero {k : ℕ} (hk : 2 < k) : cartF i₀ c k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  rfl

theorem cartE_mul (hc : c i₀ = 2) (a b : ℕ) :
    cartE i₀ c a * cartE i₀ c b = ((a + b).choose a : ℤ) • cartE i₀ c (a + b) := by
  rcases a with _ | _ | _ | a
  · simp [cartE]
  · rcases b with _ | _ | _ | b
    · simp [cartE]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, hc]
      · fin_cases r <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · rw [show 1 + (b + 3) = b + 3 + 1 by omega]
      simp [cartE]
  · rcases b with _ | _ | b
    · simp [cartE]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · rcases b with _ | b
      · ext (r | t) (r' | t')
        · fin_cases r <;> fin_cases r' <;>
            simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · fin_cases r <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · fin_cases r' <;> simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · simp [cartE, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · rw [show 2 + (b + 1 + 2) = b + 2 + 3 by omega]
        simp [cartE]
  · rw [show a + 3 + b = a + b + 3 by omega]
    simp [cartE]

theorem cartF_mul (hc : c i₀ = 2) (a b : ℕ) :
    cartF i₀ c a * cartF i₀ c b = ((a + b).choose a : ℤ) • cartF i₀ c (a + b) := by
  rcases a with _ | _ | _ | a
  · simp [cartF]
  · rcases b with _ | _ | _ | b
    · simp [cartF]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, hc]
      · fin_cases r <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · rw [show 1 + (b + 3) = b + 3 + 1 by omega]
      simp [cartF]
  · rcases b with _ | _ | b
    · simp [cartF]
    · ext (r | t) (r' | t')
      · fin_cases r <;> fin_cases r' <;>
          simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · fin_cases r' <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
    · rcases b with _ | b
      · ext (r | t) (r' | t')
        · fin_cases r <;> fin_cases r' <;>
            simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · fin_cases r <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · fin_cases r' <;> simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
        · simp [cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
      · rw [show 2 + (b + 1 + 2) = b + 2 + 3 by omega]
        simp [cartF]
  · rw [show a + 3 + b = a + b + 3 by omega]
    simp [cartF]

theorem cart_upper_three (s : R) :
    cart i₀ c !![1, s; 0, 1] =
      ∑ k ∈ Finset.range 3, s ^ k • (cartE i₀ c k).map (Int.castRingHom R) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cart, cartE, Finset.sum_range_succ, Matrix.sum_apply]
  · fin_cases r <;> simp [cart, cartE, Finset.sum_range_succ, Matrix.sum_apply, mul_comm]
  · fin_cases r' <;> simp [cart, cartE, Finset.sum_range_succ, Matrix.sum_apply]
  · simp [cart, cartE, Finset.sum_range_succ, Matrix.sum_apply, one_apply]

theorem cart_lower_three (s : R) :
    cart i₀ c !![1, 0; s, 1] =
      ∑ k ∈ Finset.range 3, s ^ k • (cartF i₀ c k).map (Int.castRingHom R) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cart, cartF, Finset.sum_range_succ, Matrix.sum_apply]
  · fin_cases r <;> simp [cart, cartF, Finset.sum_range_succ, Matrix.sum_apply, mul_comm]
  · fin_cases r' <;> simp [cart, cartF, Finset.sum_range_succ, Matrix.sum_apply]
  · simp [cart, cartF, Finset.sum_range_succ, Matrix.sum_apply, one_apply]

theorem cart_upper {N : ℕ} (hN : 2 < N) (s : R) :
    cart i₀ c !![1, s; 0, 1] =
      ∑ k ∈ Finset.range N, s ^ k • (cartE i₀ c k).map (Int.castRingHom R) := by
  rw [cart_upper_three]
  refine sum_range_eq_of_eq_zero (a := 3) (fun k hk => ?_) le_rfl hN
  rw [cartE_eq_zero i₀ c (by omega)]
  simp

theorem cart_lower {N : ℕ} (hN : 2 < N) (s : R) :
    cart i₀ c !![1, 0; s, 1] =
      ∑ k ∈ Finset.range N, s ^ k • (cartF i₀ c k).map (Int.castRingHom R) := by
  rw [cart_lower_three]
  refine sum_range_eq_of_eq_zero (a := 3) (fun k hk => ?_) le_rfl hN
  rw [cartF_eq_zero i₀ c (by omega)]
  simp

theorem cart_diag (t u : R) :
    cart i₀ c !![t, 0; 0, u] = diagonal (Sum.elim ![u ^ 2, t ^ 2] 1) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cart]
  · fin_cases r <;> simp [cart]
  · fin_cases r' <;> simp [cart]
  · simp [cart, diagonal_apply]

/-- The level of a vector of the Cartan block along the root: `-1` for `v₋`, `1` for `v₊` and
`0` for the Cartan vectors. -/
def cartLevel : Fin 2 ⊕ ι → ℤ :=
  Sum.elim ![-1, 1] 0

theorem cartE_ne_zero {k : ℕ} {r r' : Fin 2 ⊕ ι} (h : cartE i₀ c k r r' ≠ 0) :
    cartLevel r = cartLevel r' + k := by
  rcases k with _ | _ | _ | k
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartE, cartLevel]
    · simp_all [cartE]
    · simp_all [cartE]
    · by_cases htt : t = t' <;> simp_all [cartE, cartLevel, one_apply]
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartE, cartLevel]
    · fin_cases r <;> simp_all [cartE, cartLevel]
    · fin_cases r' <;> simp_all [cartE, cartLevel]
    · simp_all [cartE]
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartE, cartLevel]
    · simp_all [cartE]
    · simp_all [cartE]
    · simp_all [cartE]
  · simp [cartE] at h

theorem cartF_ne_zero {k : ℕ} {r r' : Fin 2 ⊕ ι} (h : cartF i₀ c k r r' ≠ 0) :
    cartLevel r + k = cartLevel r' := by
  rcases k with _ | _ | _ | k
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartF, cartLevel]
    · simp_all [cartF]
    · simp_all [cartF]
    · by_cases htt : t = t' <;> simp_all [cartF, cartLevel, one_apply]
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartF, cartLevel]
    · fin_cases r <;> simp_all [cartF, cartLevel]
    · fin_cases r' <;> simp_all [cartF, cartLevel]
    · simp_all [cartF]
  · rcases r with r | t <;> rcases r' with r' | t'
    · fin_cases r <;> fin_cases r' <;> simp_all [cartF, cartLevel]
    · simp_all [cartF]
    · simp_all [cartF]
    · simp_all [cartF]
  · simp [cartF] at h

theorem cart_weyl_ne_zero {r r' : Fin 2 ⊕ ι}
    (h : cart i₀ c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) r r' ≠ 0) :
    cartLevel r = -cartLevel r' := by
  rcases r with r | t <;> rcases r' with r' | t'
  · fin_cases r <;> fin_cases r' <;> simp_all [cart, cartLevel]
  · fin_cases r <;> simp_all [cart]
  · fin_cases r' <;> simp_all [cart]
  · simp [cartLevel]

/-- The bracket of the raising and lowering operators on the Cartan block is diagonal with
entries `2 · cartLevel`. -/
theorem cartE_one_mul_cartF_one_sub (hc : c i₀ = 2) :
    cartE i₀ c 1 * cartF i₀ c 1 - cartF i₀ c 1 * cartE i₀ c 1 =
      diagonal fun r => 2 * cartLevel r := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;>
      simp [cartE, cartF, cartLevel, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, hc]
  · fin_cases r <;> simp [cartE, cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
  · fin_cases r' <;> simp [cartE, cartF, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ]
  · simp [cartE, cartF, cartLevel, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
      diagonal_apply]

end Cartan

end Langlands.GroupScheme.SplitExistence
