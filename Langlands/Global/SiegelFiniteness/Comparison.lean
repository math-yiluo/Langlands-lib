import Langlands.Automorphic.CuspidalL2.SiegelCover

/-!
# Comparison of torus coordinates

Real-variable consequences of the key inequality. Let `x, x'` be torus coordinates in the chamber
with constant `K ≥ 0` (consecutive increases at most `K`), and let `P t j`, `P' t j` be relations
(nonvanishing of the `(t, j)` entries of `γ⁻¹` and of `γ`) with

* `P t j → x' j ≤ x t + β` and `P' t j → x j ≤ x' t + β`,
* for every `i` some `P t j` and some `P' t j` hold with `j ≤ i ≤ t`.

Then `x` and `x'` are comparable, `|x_i - x'_i| ≤ Δ = β + 2nK`; a drop of `x` larger than
`G = Δ + β + 2nK` at position `s` forces `¬ P' t j` for `t ≥ s > j`; and for all `a, b` either
`x'_a - x_b` is bounded by `Λ = Δ + nK + nG`, or there is such a drop at some `s` with
`a < s ≤ b`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

open Automorphic.CuspidalL2

variable {n : ℕ}

/-- In the chamber, later coordinates exceed earlier ones by at most `nK`. -/
theorem chamber_le {K : ℝ} (hK : 0 ≤ K) {x : Fin n → ℝ} (hx : Chamber K x) {i j : Fin n}
    (hij : i ≤ j) : x j ≤ x i + n * K := by
  have := sub_le_of_adjacent (fun k => -x k) hK
    (fun a b hab => by have := hx a b hab; show -x a - -x b ≤ K; linarith) i j hij
  linarith

/-- Bounded drops on `(a, b]` bound `x a - x b`. -/
theorem sub_le_of_drops {x : Fin n → ℝ} {G : ℝ} (hG : 0 ≤ G) (a b : Fin n) (hab : a ≤ b)
    (h : ∀ p q : Fin n, p.val + 1 = q.val → a.val < q.val → q.val ≤ b.val → x p - x q ≤ G) :
    x a - x b ≤ n * G := by
  have key : ∀ k : ℕ, ∀ j : Fin n, j.val = a.val + k → j ≤ b → x a - x j ≤ k * G := by
    intro k
    induction k with
    | zero =>
      intro j hj _
      have : j = a := Fin.ext (by omega)
      subst this
      simp
    | succ k ih =>
      intro j hj hjb
      have hjb' : j.val ≤ b.val := hjb
      have h1 := ih ⟨a.val + k, by omega⟩ rfl (show a.val + k ≤ b.val by omega)
      have h2 := h ⟨a.val + k, by omega⟩ j (by simp only; omega) (by omega) hjb'
      push_cast
      linarith
  have hle : a.val ≤ b.val := hab
  have hk := key (b.val - a.val) b (by omega) le_rfl
  have hkn : ((b.val - a.val : ℕ) : ℝ) ≤ n := by
    have := b.isLt
    exact_mod_cast (by omega : b.val - a.val ≤ n)
  exact hk.trans (mul_le_mul_of_nonneg_right hkn hG)

variable {K β : ℝ} {x x' : Fin n → ℝ} {P : Fin n → Fin n → Prop}

/-- **Comparability.** -/
theorem le_add_of_key (hK : 0 ≤ K) (hx : Chamber K x) (hx' : Chamber K x')
    (hkey : ∀ t j, P t j → x' j ≤ x t + β) (hP : ∀ i, ∃ t j, i ≤ t ∧ j ≤ i ∧ P t j)
    (i : Fin n) : x' i ≤ x i + (β + 2 * n * K) := by
  obtain ⟨t, j, hit, hji, hPtj⟩ := hP i
  have h1 := chamber_le hK hx' hji
  have h2 := hkey t j hPtj
  have h3 := chamber_le hK hx hit
  linarith

/-- **A large drop forces a vanishing block.** -/
theorem not_of_drop (hK : 0 ≤ K) (hx : Chamber K x) {Δ : ℝ}
    (hcomp : ∀ i, x' i ≤ x i + Δ) (hkey : ∀ t j, P t j → x j ≤ x' t + β)
    (p q : Fin n) (hpq : p.val + 1 = q.val) (hdrop : Δ + β + 2 * n * K < x p - x q)
    (t j : Fin n) (ht : q.val ≤ t.val) (hj : j.val < q.val) : ¬ P t j := by
  intro hPtj
  have h1 := hkey t j hPtj
  have h2 := hcomp t
  have h3 := chamber_le hK hx (show q ≤ t from ht)
  have h4 := chamber_le hK hx (show j ≤ p from Fin.le_def.mpr (by omega))
  linarith

/-- **Bounded ratio or a large drop.** -/
theorem le_or_exists_drop (hK : 0 ≤ K) (hx' : Chamber K x') {Δ G : ℝ}
    (hG : 0 ≤ G) (hcomp : ∀ i, x' i ≤ x i + Δ) (a b : Fin n) :
    x' a - x b ≤ Δ + n * K + n * G ∨
      ∃ p q : Fin n, p.val + 1 = q.val ∧ a.val < q.val ∧ q.val ≤ b.val ∧ G < x p - x q := by
  have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK
  have hnG : 0 ≤ (n : ℝ) * G := mul_nonneg (Nat.cast_nonneg n) hG
  rcases le_total b a with hba | hab
  · left
    have h1 := chamber_le hK hx' hba
    have h2 := hcomp b
    linarith
  · by_cases hdrop : ∃ p q : Fin n, p.val + 1 = q.val ∧ a.val < q.val ∧ q.val ≤ b.val ∧
        G < x p - x q
    · exact Or.inr hdrop
    · left
      push Not at hdrop
      have h1 := sub_le_of_drops hG a b hab fun p q hpq haq hqb => hdrop p q hpq haq hqb
      have h2 := hcomp a
      linarith

end Langlands.Global.SiegelFiniteness
