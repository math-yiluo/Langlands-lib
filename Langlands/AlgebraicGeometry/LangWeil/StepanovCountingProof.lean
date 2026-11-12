import Langlands.AlgebraicGeometry.LangWeil.StepanovCountingStatement
import Mathlib.Tactic

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open scoped BigOperators

private theorem sum_rootMultiplicity_le {F : Type u} [Field F] [Fintype F]
    (s : Finset F) (h : Polynomial F) :
    ∑ x ∈ s, h.rootMultiplicity x ≤ h.natDegree := by
  classical
  calc
    ∑ x ∈ s, h.rootMultiplicity x ≤ ∑ x : F, h.rootMultiplicity x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = h.roots.card := by
      simp_rw [← Polynomial.count_roots]
      exact Multiset.sum_count_eq_card (fun x _ => Finset.mem_univ x)
    _ ≤ h.natDegree := Polynomial.card_roots' h

/-- Finite root counting after the auxiliary norm polynomials have been constructed. -/
private theorem norm_polynomial_count_bound {F : Type u} [Field F] [Fintype F]
    (r : F → ℕ) (s : Finset F) (n B E M : ℕ)
    (hn : 0 < n) (hM : 0 < M)
    (hbad : Fintype.card F ≤ s.card + B)
    (hr : ∀ x, r x ≤ n)
    (h₁ h₂ : Polynomial F)
    (hd₁ : h₁.natDegree < Fintype.card F * (M + E))
    (hd₂ : h₂.natDegree < Fintype.card F * ((n - 1) * M + E))
    (hmult : ∀ x ∈ s,
      M * r x ≤ h₁.rootMultiplicity x ∧
      M * (n - r x) ≤ h₂.rootMultiplicity x) :
    (M : ℝ) * |(∑ x : F, r x : ℕ) - (Fintype.card F : ℝ)| <
      (Fintype.card F : ℝ) * E + n * B * M := by
  classical
  have hz₁ : M * ∑ x ∈ s, r x < Fintype.card F * (M + E) := by
    calc
      M * ∑ x ∈ s, r x = ∑ x ∈ s, M * r x := Finset.mul_sum ..
      _ ≤ ∑ x ∈ s, h₁.rootMultiplicity x :=
        Finset.sum_le_sum (fun x hx => (hmult x hx).1)
      _ ≤ h₁.natDegree := sum_rootMultiplicity_le s h₁
      _ < _ := hd₁
  have hz₂ : M * ∑ x ∈ s, (n - r x) <
      Fintype.card F * ((n - 1) * M + E) := by
    calc
      M * ∑ x ∈ s, (n - r x) = ∑ x ∈ s, M * (n - r x) := Finset.mul_sum ..
      _ ≤ ∑ x ∈ s, h₂.rootMultiplicity x :=
        Finset.sum_le_sum (fun x hx => (hmult x hx).2)
      _ ≤ h₂.natDegree := sum_rootMultiplicity_le s h₂
      _ < _ := hd₂
  have hzsum : (∑ x ∈ s, r x) + (∑ x ∈ s, (n - r x)) = s.card * n := by
    rw [← Finset.sum_add_distrib]
    simp only [Nat.add_sub_of_le (hr _), Finset.sum_const, smul_eq_mul]
  have hcomplcard : sᶜ.card ≤ B := by
    have hc := Finset.card_add_card_compl s
    omega
  have hcompl : ∑ x ∈ sᶜ, r x ≤ n * B := by
    calc
      ∑ x ∈ sᶜ, r x ≤ ∑ _x ∈ sᶜ, n :=
        Finset.sum_le_sum (fun x _ => hr x)
      _ = sᶜ.card * n := by simp
      _ ≤ B * n := Nat.mul_le_mul_right n hcomplcard
      _ = n * B := Nat.mul_comm ..
  have hpart := Finset.sum_add_sum_compl s r
  have hAupper : (∑ x : F, r x) ≤ (∑ x ∈ s, r x) + n * B := by omega
  have hAlower : (∑ x ∈ s, r x) ≤ ∑ x : F, r x :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnr : (0 : ℝ) ≤ n := by positivity
  have hbadR : (Fintype.card F : ℝ) ≤ (s.card : ℝ) + B := by exact_mod_cast hbad
  have hAupperR : ((∑ x : F, r x : ℕ) : ℝ) ≤
      ((∑ x ∈ s, r x : ℕ) : ℝ) + (n : ℝ) * B := by exact_mod_cast hAupper
  have hAlowerR : ((∑ x ∈ s, r x : ℕ) : ℝ) ≤
      ((∑ x : F, r x : ℕ) : ℝ) := by exact_mod_cast hAlower
  have hzsumR : ((∑ x ∈ s, r x : ℕ) : ℝ) +
      ((∑ x ∈ s, (n - r x) : ℕ) : ℝ) = (s.card : ℝ) * n := by
    exact_mod_cast hzsum
  have hz₁R : (M : ℝ) * ((∑ x ∈ s, r x : ℕ) : ℝ) <
      (Fintype.card F : ℝ) * (M + E) := by exact_mod_cast hz₁
  have hz₂R : (M : ℝ) * ((∑ x ∈ s, (n - r x) : ℕ) : ℝ) <
      (Fintype.card F : ℝ) * (((n : ℝ) - 1) * M + E) := by
    have hn1 : (1 : ℕ) ≤ n := hn
    exact_mod_cast hz₂
  have hupper : (M : ℝ) * (((∑ x : F, r x : ℕ) : ℝ) -
      (Fintype.card F : ℝ)) < (Fintype.card F : ℝ) * E + n * B * M := by
    nlinarith [mul_le_mul_of_nonneg_left hAupperR hMr.le]
  have hlower : (M : ℝ) * ((Fintype.card F : ℝ) -
      ((∑ x : F, r x : ℕ) : ℝ)) < (Fintype.card F : ℝ) * E + n * B * M := by
    nlinarith [mul_le_mul_of_nonneg_left hbadR (mul_nonneg hMr.le hnr),
      mul_le_mul_of_nonneg_left hAlowerR hMr.le,
      congrArg (fun z : ℝ => (M : ℝ) * z) hzsumR]
  have habs : (M : ℝ) * |((∑ x : F, r x : ℕ) : ℝ) -
      (Fintype.card F : ℝ)| =
      |(M : ℝ) * (((∑ x : F, r x : ℕ) : ℝ) - (Fintype.card F : ℝ))| := by
    rw [abs_mul, abs_of_pos hMr]
  rw [habs, abs_lt]
  constructor <;> linarith

private theorem parameter_square_bound (n t : ℝ) (hn : 2 ≤ n)
    (ht : 3 * (n + 1) < t) :
    (n ^ 2 + 1) * (t + 2) ^ 2 < (n + 1) ^ 2 * t ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hd : 0 ≤ t - 3 * (n + 1) := by linarith
  have hc : 0 ≤ 8 * n ^ 2 + 12 * n - 4 := by nlinarith [sq_nonneg n]
  have hk : 0 < 6 * n ^ 3 + 20 * n ^ 2 + 6 * n - 16 := by
    nlinarith [pow_nonneg hn0 3, sq_nonneg (n - 2)]
  nlinarith [mul_nonneg hn0 (sq_nonneg (t - 3 * (n + 1))),
    mul_nonneg hc hd]

private theorem threshold_sqrt (m n q : ℕ)
    (hq : 9 * (m + 1) ^ 2 * (n + 1) ^ 2 < q) :
    3 * ((m : ℝ) + 1) * (n + 1) < Real.sqrt q := by
  have hqR : (9 : ℝ) * (m + 1) ^ 2 * (n + 1) ^ 2 < q := by
    exact_mod_cast hq
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  nlinarith [sq_nonneg (3 * ((m : ℝ) + 1) * (n + 1) + Real.sqrt q)]

/-- A ceiling choice of the integer parameter avoids losing the strict final bound. -/
private theorem exists_stepanov_parameter (m n q : ℕ)
    (hn : 2 ≤ n) (hnm : n ≤ m)
    (hq : 9 * (m + 1) ^ 2 * (n + 1) ^ 2 < q) :
    ∃ M : ℕ, 0 < M ∧ m ≤ M ∧
      M ^ 2 * (n ^ 2 + 1) + (M + m) * n ^ 2 < q ∧ M * n ≤ q ∧
      (q : ℝ) ≤ (M : ℝ) * (n + 1) * Real.sqrt q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hqR : (9 : ℝ) * (m + 1) ^ 2 * (n + 1) ^ 2 < q := by
    exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt hq0
  have hs : 3 * ((m : ℝ) + 1) * (n + 1) < Real.sqrt q := by
    nlinarith [sq_nonneg (3 * ((m : ℝ) + 1) * (n + 1) + Real.sqrt q)]
  let t : ℝ := Real.sqrt q / (n + 1)
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hteq : t * (n + 1) = Real.sqrt q := by
    dsimp [t]
    exact div_mul_cancel₀ _ hn1.ne'
  have ht : 3 * ((m : ℝ) + 1) < t := by nlinarith
  have ht0 : 0 ≤ t := by linarith
  let M : ℕ := Nat.ceil t
  have hMlo : t ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
  have hMposR : (0 : ℝ) < M := by linarith
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have hmM : m ≤ M := by exact_mod_cast (show (m : ℝ) ≤ M by linarith)
  have htN : 3 * ((n : ℝ) + 1) < t := by linarith
  have htSq := parameter_square_bound n t hnR htN
  have hM1sq : ((M : ℝ) + 1) ^ 2 ≤ (t + 2) ^ 2 := by nlinarith
  have hMbound : ((n : ℝ) ^ 2 + 1) * ((M : ℝ) + 1) ^ 2 < q := by
    have hh := mul_le_mul_of_nonneg_left hM1sq (by positivity : (0 : ℝ) ≤ n ^ 2 + 1)
    nlinarith [sq_nonneg (t * (n + 1) - Real.sqrt q)]
  have hMboundN : (n ^ 2 + 1) * (M + 1) ^ 2 < q := by exact_mod_cast hMbound
  have hcore :
      M ^ 2 * (n ^ 2 + 1) + (M + m) * n ^ 2 < q := by
    nlinarith
  have hMn : M * n ≤ q := by nlinarith
  refine ⟨M, hMpos, hmM, hcore, hMn, ?_⟩
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hMlo hn1.le) hs0
  nlinarith

private theorem final_error_comparison (m n : ℝ)
    (hn : 2 ≤ n) (hnm : n ≤ m) (s : ℝ)
    (hs : 3 * (m + 1) * (n + 1) < s) :
    (2 * m * (n - 1) + 1) * (n + 1) * s + 2 * m * n ^ 2 <
      2 * m * n ^ 2 * s := by
  have hm : 2 ≤ m := hn.trans hnm
  have hm0 : 0 ≤ m := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := by nlinarith
  have haux : m ^ 2 * n ≤ (m - 1) * (m + 1) * (n + 1) := by
    nlinarith [mul_nonneg hm0 (show 0 ≤ m - 2 by linarith)]
  have hfirst : 2 * m * n ^ 2 ≤ 3 * m ^ 2 * n := by
    nlinarith [mul_nonneg (show 0 ≤ m - n by linarith) (mul_nonneg hm0 hn0),
      mul_nonneg (sq_nonneg m) hn0]
  have hgap : 2 * m * n ^ 2 < (2 * m - n - 1) * s := by
    calc
      2 * m * n ^ 2 ≤ 3 * m ^ 2 * n := hfirst
      _ ≤ 3 * ((m - 1) * (m + 1) * (n + 1)) := by linarith
      _ < (m - 1) * s := by
        nlinarith [mul_lt_mul_of_pos_left hs (show 0 < m - 1 by linarith)]
      _ ≤ (2 * m - n - 1) * s :=
        mul_le_mul_of_nonneg_right (by linarith) hs0
  nlinarith

/-- The finite counting and parameter step in Schmidt's method. -/
theorem stepanovCounting : StepanovCountingStatement.{u} := by
  intro F _ _ r m n hn hnm hq haux
  obtain ⟨M, hM, _hmM, hcore, hMn, hqM⟩ :=
    exists_stepanov_parameter m n (Fintype.card F) hn hnm hq
  obtain ⟨s, h₁, h₂, hs, hr, hd₁, hd₂, hmult⟩ := haux M hM hcore hMn
  have hc := norm_polynomial_count_bound r s n (2 * m * n)
    (2 * m * (n - 1) + 1) M (by omega) hM hs.le hr h₁ h₂ hd₁ hd₂ hmult
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hE : ((2 * m * (n - 1) + 1 : ℕ) : ℝ) = 2 * m * ((n : ℝ) - 1) + 1 := by
    push_cast [Nat.cast_sub hn1]
    rfl
  rw [hE] at hc
  push_cast at hc
  have hnum := final_error_comparison m n hnR hnmR (Real.sqrt (Fintype.card F))
    (threshold_sqrt m n (Fintype.card F) hq)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have herror := mul_le_mul_of_nonneg_right hqM
    (show (0 : ℝ) ≤ 2 * m * ((n : ℝ) - 1) + 1 by
      have hnn : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      positivity)
  have hstrict := mul_lt_mul_of_pos_left hnum hMr
  push_cast
  nlinarith

end Langlands.AlgebraicGeometry.LangWeil
