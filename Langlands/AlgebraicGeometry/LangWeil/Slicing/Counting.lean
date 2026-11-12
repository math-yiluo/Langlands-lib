import Mathlib

/-!
# Counting points on hyperplane sections over a finite field

Elementary counting used in the hyperplane-slicing step of the Lang–Weil estimate. Affine
hyperplanes of `κⁿ` are parametrized by `α : Option (Fin n) → κ`, with constant term `α none`
and linear coefficients `α (some i)`.
-/

open Finset

namespace Langlands.AlgebraicGeometry.LangWeil.Slicing

section DoubleCounting

variable {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]

/-- For a fixed point `w`, the parameters with nonzero linear part whose hyperplane passes
through `w` are in bijection with the nonzero linear parts. -/
theorem card_filter_hyperplane_through (n : ℕ) (w : Fin n → κ) :
    #(univ.filter (fun α : Option (Fin n) → κ =>
      (fun i => α (some i)) ≠ 0 ∧ α none + ∑ i, α (some i) * w i = 0)) =
      Fintype.card κ ^ n - 1 := by
  have h : #(univ.filter (fun α : Option (Fin n) → κ =>
      (fun i => α (some i)) ≠ 0 ∧ α none + ∑ i, α (some i) * w i = 0)) =
      #(univ.filter (fun a : Fin n → κ => a ≠ 0)) := by
    refine card_nbij' (fun α i => α (some i))
      (fun a o => o.elim (-(∑ i, a i * w i)) a) ?_ ?_ ?_ ?_
    · intro α hα
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hα ⊢
      exact hα.1
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      refine ⟨ha, ?_⟩
      simp only [Option.elim]
      ring
    · intro α hα
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hα
      funext o
      cases o with
      | none =>
        simp only [Option.elim]
        linear_combination -hα.2
      | some i => rfl
    · intro a _
      rfl
  rw [h, filter_ne' univ (0 : Fin n → κ), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fun, Fintype.card_fin]

/-- Double counting: summing, over all affine hyperplanes with nonzero linear part, the number
of points of a finite family lying on the hyperplane gives the size of the family times
`#κ ^ n - 1`. -/
theorem sum_card_filter_hyperplane {ι : Type*} [Fintype ι] (n : ℕ) (v : ι → Fin n → κ) :
    ∑ α ∈ univ.filter (fun α : Option (Fin n) → κ => (fun i => α (some i)) ≠ 0),
      #(univ.filter (fun x => α none + ∑ i, α (some i) * v x i = 0)) =
      Fintype.card ι * (Fintype.card κ ^ n - 1) := by
  classical
  simp_rw [card_filter]
  rw [sum_comm]
  simp_rw [← sum_filter]
  have h : ∀ x : ι, ∑ α ∈ (univ.filter (fun α : Option (Fin n) → κ =>
      (fun i => α (some i)) ≠ 0)).filter (fun α => α none + ∑ i, α (some i) * v x i = 0),
      (1 : ℕ) = Fintype.card κ ^ n - 1 := by
    intro x
    rw [← card_eq_sum_ones, filter_filter]
    exact card_filter_hyperplane_through n (v x)
  rw [sum_congr rfl (fun x _ => h x), sum_const, card_univ, smul_eq_mul]

end DoubleCounting

section SchwartzZippel

variable {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]

/-- The Schwartz–Zippel bound over a finite field, for polynomials in `m + 1` variables indexed
by an arbitrary finite type: a nonzero polynomial vanishes at no more than
`totalDegree p * #κ ^ m` points. -/
theorem card_filter_eval_eq_zero_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    {p : MvPolynomial σ κ} (hp : p ≠ 0) (m : ℕ) (hσ : Fintype.card σ = m + 1) :
    #(univ.filter (fun α : σ → κ => MvPolynomial.eval α p = 0)) ≤
      p.totalDegree * Fintype.card κ ^ m := by
  let e : σ ≃ Fin (m + 1) := (Fintype.equivFin σ).trans (finCongr hσ)
  set p' : MvPolynomial (Fin (m + 1)) κ := MvPolynomial.rename e p with hp'
  have hp'0 : p' ≠ 0 := by
    intro h
    apply hp
    apply MvPolynomial.rename_injective e e.injective
    rw [← hp', h, map_zero]
  have hdeg : p'.totalDegree ≤ p.totalDegree := MvPolynomial.totalDegree_rename_le _ _
  have hcard : #(univ.filter (fun α : σ → κ => MvPolynomial.eval α p = 0)) =
      #(univ.filter (fun f : Fin (m + 1) → κ => MvPolynomial.eval f p' = 0)) := by
    refine card_nbij' (fun α => α ∘ e.symm) (fun f => f ∘ e) ?_ ?_ ?_ ?_
    · intro α hα
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hα ⊢
      rw [hp', MvPolynomial.eval_rename]
      have : (α ∘ e.symm) ∘ e = α := by
        funext i
        simp
      rw [this]
      exact hα
    · intro f hf
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      rw [hp', MvPolynomial.eval_rename] at hf
      exact hf
    · intro α _
      funext i
      simp
    · intro f _
      funext i
      simp
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp'0 (univ : Finset κ)
  simp only [Fintype.piFinset_univ, card_univ] at hsz
  have hq : (0 : ℚ≥0) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hq] at hsz
  rw [hcard]
  have : (#(univ.filter (fun f : Fin (m + 1) → κ => MvPolynomial.eval f p' = 0)) : ℚ≥0) ≤
      p.totalDegree * Fintype.card κ ^ m := by
    have h1 : (#(univ.filter (fun f : Fin (m + 1) → κ => MvPolynomial.eval f p' = 0)) : ℚ≥0) *
        Fintype.card κ ≤ (p.totalDegree * Fintype.card κ ^ m) * Fintype.card κ := by
      calc _ ≤ _ := hsz
        _ = (p'.totalDegree : ℚ≥0) * Fintype.card κ ^ m * Fintype.card κ := by ring
        _ ≤ _ := by gcongr
    exact le_of_mul_le_mul_right h1 hq
  exact_mod_cast this

end SchwartzZippel

section Containing

variable {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]

/-- The parameters with nonzero linear part whose hyperplane equation lies in a proper ideal `I`
of a `κ`-algebra `T` are few when some coordinate function `g i₀` is not congruent to a constant
modulo `I`: they form, together with `0`, a linear subspace of dimension at most `n - 1`. -/
theorem card_filter_mem_ideal_mul_le {T : Type*} [CommRing T] [Algebra κ T] (I : Ideal T)
    [DecidablePred (· ∈ I)] (hI : I ≠ ⊤) (n : ℕ) (g : Fin n → T) (i₀ : Fin n)
    (hi₀ : ∀ c : κ, g i₀ - algebraMap κ T c ∉ I) :
    (#(univ.filter (fun α : Option (Fin n) → κ => (fun i => α (some i)) ≠ 0 ∧
      algebraMap κ T (α none) + ∑ i, α (some i) • g i ∈ I)) + 1) * Fintype.card κ ≤
      Fintype.card κ ^ n := by
  classical
  let L : (Option (Fin n) → κ) →ₗ[κ] T ⧸ I :=
    (Ideal.Quotient.mkₐ κ I).toLinearMap ∘ₗ
      ((Algebra.linearMap κ T) ∘ₗ LinearMap.proj none +
        ∑ i, (LinearMap.toSpanSingleton κ T (g i)) ∘ₗ LinearMap.proj (some i))
  have hL : ∀ α, L α = Ideal.Quotient.mk I
      (algebraMap κ T (α none) + ∑ i, α (some i) • g i) := by
    intro α
    simp [L]
  -- the range of `L` has dimension at least two
  have hrange : 2 ≤ Module.finrank κ (LinearMap.range L) := by
    let v : Fin 2 → LinearMap.range L :=
      ![⟨L (Pi.single none 1), LinearMap.mem_range_self _ _⟩,
        ⟨L (Pi.single (some i₀) 1), LinearMap.mem_range_self _ _⟩]
    have hv : LinearIndependent κ v := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hst' : s • L (Pi.single none 1) + t • L (Pi.single (some i₀) 1) = 0 := by
        have := congrArg Subtype.val hst
        simpa using this
      rw [hL, hL] at hst'
      simp only [Pi.single_eq_same, ne_eq, reduceCtorEq, not_false_eq_true,
        Pi.single_eq_of_ne, map_one, zero_smul, Finset.sum_const_zero,
        add_zero, map_zero, zero_add] at hst'
      rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj])
        (by simp)] at hst'
      simp only [Pi.single_eq_same, one_smul] at hst'
      replace hst' : algebraMap κ T s + t • g i₀ ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [Algebra.smul_def] using hst'
      by_cases ht : t = 0
      · subst ht
        refine ⟨?_, rfl⟩
        by_contra hs
        apply hI
        rw [Ideal.eq_top_iff_one]
        have : algebraMap κ T s ∈ I := by simpa using hst'
        have h1 := I.mul_mem_left (algebraMap κ T s⁻¹) this
        rwa [← map_mul, inv_mul_cancel₀ hs, map_one] at h1
      · exfalso
        apply hi₀ (-(s / t))
        have h1 := I.mul_mem_left (algebraMap κ T t⁻¹) hst'
        convert h1 using 1
        rw [Algebra.smul_def, mul_add, ← mul_assoc, ← map_mul (algebraMap κ T) t⁻¹ t,
          inv_mul_cancel₀ ht, map_one, one_mul, map_neg, div_eq_inv_mul, map_mul]
        ring
    simpa using hv.fintype_card_le_finrank
  have hker : Module.finrank κ (LinearMap.ker L) + 1 ≤ n := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin] at this
    omega
  have hfin : Module.Finite κ (LinearMap.ker L) :=
    Module.Finite.of_injective (LinearMap.ker L).subtype Subtype.val_injective
  have hcardker :
      Nat.card (LinearMap.ker L) = Fintype.card κ ^ Module.finrank κ (LinearMap.ker L) := by
    rw [Module.natCard_eq_pow_finrank (K := κ), Nat.card_eq_fintype_card]
  -- the counted set, together with `0`, lies in the kernel
  have hsub : insert 0 (univ.filter (fun α : Option (Fin n) → κ => (fun i => α (some i)) ≠ 0 ∧
      algebraMap κ T (α none) + ∑ i, α (some i) • g i ∈ I)) ⊆
      univ.filter (fun α => α ∈ LinearMap.ker L) := by
    intro α hα
    simp only [mem_insert, mem_filter, mem_univ, true_and] at hα ⊢
    rcases hα with rfl | ⟨_, hα⟩
    · exact Submodule.zero_mem _
    · rw [LinearMap.mem_ker, hL, Ideal.Quotient.eq_zero_iff_mem]
      exact hα
  have h0 : (0 : Option (Fin n) → κ) ∉ univ.filter (fun α : Option (Fin n) → κ =>
      (fun i => α (some i)) ≠ 0 ∧ algebraMap κ T (α none) + ∑ i, α (some i) • g i ∈ I) := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro h
    exact absurd rfl h
  have hle := card_le_card hsub
  rw [card_insert_of_notMem h0] at hle
  have hkercard : #(univ.filter (fun α : Option (Fin n) → κ => α ∈ LinearMap.ker L)) =
      Nat.card (LinearMap.ker L) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hkercard, hcardker] at hle
  calc _ ≤ Fintype.card κ ^ Module.finrank κ (LinearMap.ker L) * Fintype.card κ :=
        Nat.mul_le_mul_right _ hle
    _ = Fintype.card κ ^ (Module.finrank κ (LinearMap.ker L) + 1) := by ring
    _ ≤ Fintype.card κ ^ n := Nat.pow_le_pow_right Fintype.card_pos hker

end Containing

section Estimate

/-- The real-number estimate comparing the two evaluations of the incidence sum. The parameter
set `Λ` (of size `P Q - Q`, where `P` stands for `Q ^ n`) is split into the parameters `Λc` whose
hyperplane contains the whole fibre (each slice has `N` points, and `(#Λc + 1) Q ≤ P`), the
exceptional parameters `Λb` (at most `D P` of them, each slice with at most `C₂ Q ^ (d + 1)`
points) and the rest (each slice satisfying the Lang–Weil estimate in dimension `d + 1`). If the
slice counts sum to `N (P - 1)`, then `N` satisfies the Lang–Weil estimate in dimension
`d + 2`. -/
theorem abs_sub_pow_le_of_slices {ι : Type*} [DecidableEq ι] (Λ Λc Λb : Finset ι)
    (hc : Λc ⊆ Λ) (hb : Λb ⊆ Λ) (hdisj : Disjoint Λc Λb) (Nα : ι → ℝ)
    (N Q P C₁ C₂ D : ℝ) (d : ℕ) (hQ : 2 ≤ Q) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hΛ : (#Λ : ℝ) = P * Q - Q) (hsum : ∑ α ∈ Λ, Nα α = N * (P - 1))
    (hcN : ∀ α ∈ Λc, Nα α = N) (hcard_c : ((#Λc : ℝ) + 1) * Q ≤ P)
    (hb0 : ∀ α ∈ Λb, 0 ≤ Nα α) (hbC : ∀ α ∈ Λb, Nα α ≤ C₂ * Q ^ (d + 1))
    (hcard_b : (#Λb : ℝ) ≤ D * P)
    (hrest : ∀ α ∈ Λ, α ∉ Λc → α ∉ Λb →
      |Nα α - Q ^ (d + 1)| ≤ C₁ * Q ^ (((d + 1 : ℕ) : ℝ) - 1 / 2)) :
    |N - Q ^ (d + 2)| ≤ 2 * (2 + D + C₁ + D * C₂) * Q ^ (((d + 2 : ℕ) : ℝ) - 1 / 2) := by
  have hQ0 : 0 < Q := by linarith
  set R := Λ \ (Λc ∪ Λb) with hR
  have hsub : Λc ∪ Λb ⊆ Λ := union_subset hc hb
  have hsplit : ∑ α ∈ Λ, Nα α = ∑ α ∈ Λc, Nα α + ∑ α ∈ Λb, Nα α + ∑ α ∈ R, Nα α := by
    rw [← sum_union hdisj, ← sum_sdiff hsub, add_comm]
  have hcardR : (#R : ℝ) = #Λ - #Λc - #Λb := by
    have h1 := card_sdiff_add_card_eq_card hsub
    rw [card_union_of_disjoint hdisj] at h1
    rw [hR]
    have h2 : ((#(Λ \ (Λc ∪ Λb)) + (#Λc + #Λb) : ℕ) : ℝ) = (#Λ : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  set m : ℝ := (#Λc : ℝ) with hm
  set b : ℝ := (#Λb : ℝ) with hbdef
  set ρ : ℝ := (#R : ℝ) with hρ
  set X : ℝ := Q ^ (d + 1) with hX
  set s : ℝ := Q ^ (1 / 2 : ℝ) with hs
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hb0' : 0 ≤ b := Nat.cast_nonneg _
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := by positivity
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow1 : Q ^ (((d + 1 : ℕ) : ℝ) - 1 / 2) = Q ^ d * s := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_add hQ0]
    congr 1
    push_cast
    ring
  have hpow2 : Q ^ (((d + 2 : ℕ) : ℝ) - 1 / 2) = X * s := by
    rw [hs, hX, ← Real.rpow_natCast, ← Real.rpow_add hQ0]
    congr 1
    push_cast
    ring
  have hXQ : Q ^ (d + 2) = X * Q := by rw [hX, pow_succ]
  have hXd : X = Q ^ d * Q := by rw [hX, pow_succ]
  -- the three partial sums
  have hsc : ∑ α ∈ Λc, Nα α = m * N := by
    rw [sum_congr rfl hcN, sum_const, nsmul_eq_mul]
  set Sb := ∑ α ∈ Λb, Nα α with hSb
  have hSb0 : 0 ≤ Sb := sum_nonneg hb0
  have hSbC : Sb ≤ b * (C₂ * X) := by
    calc Sb ≤ ∑ _α ∈ Λb, C₂ * X := sum_le_sum hbC
      _ = b * (C₂ * X) := by rw [sum_const, nsmul_eq_mul]
  set E := ∑ α ∈ R, (Nα α - X) with hE
  have hSR : ∑ α ∈ R, Nα α = ρ * X + E := by
    rw [hE, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  have hEle : |E| ≤ ρ * (C₁ * (Q ^ d * s)) := by
    calc |E| ≤ ∑ α ∈ R, |Nα α - X| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α ∈ R, C₁ * (Q ^ d * s) := by
        apply sum_le_sum
        intro α hα
        rw [hR, mem_sdiff, mem_union, not_or] at hα
        rw [← hpow1]
        exact hrest α hα.1 hα.2.1 hα.2.2
      _ = ρ * (C₁ * (Q ^ d * s)) := by rw [sum_const, nsmul_eq_mul]
  -- the key identity
  have hkey : (N - Q ^ (d + 2)) * (P - 1 - m) = Sb - (m + b) * X + m * (X * Q) + E := by
    rw [hXQ]
    have := hsum
    rw [hsplit, hsc, hSR] at this
    have hρ' : ρ = P * Q - Q - m - b := by rw [hcardR, hΛ]
    rw [hρ'] at this
    linear_combination -this
  -- size estimates
  have hm2 : (m + 1) * 2 ≤ (m + 1) * Q := mul_le_mul_of_nonneg_left hQ (by linarith)
  have hP2 : 2 ≤ P := by linarith
  have hmQ : m * Q ≤ P := by
    have : (m + 1) * Q = m * Q + Q := by ring
    linarith
  have hmP : m ≤ P := (le_mul_of_one_le_right hm0 (by linarith)).trans hmQ
  have hρP : ρ ≤ P * Q := by
    have : ρ = P * Q - Q - m - b := by rw [hcardR, hΛ]
    linarith
  have hhalf : P / 2 ≤ P - 1 - m := by linarith
  have hbound : |Sb - (m + b) * X + m * (X * Q) + E| ≤
      (2 + D + C₁ + D * C₂) * P * (X * s) := by
    have h1 : |Sb - (m + b) * X + m * (X * Q) + E| ≤ Sb + (m + b) * X + m * Q * X + |E| := by
      have := abs_add_le (Sb - (m + b) * X + m * (X * Q)) E
      have h2 := abs_add_le (Sb - (m + b) * X) (m * (X * Q))
      have h3 := abs_sub (Sb) ((m + b) * X)
      rw [abs_of_nonneg hSb0, abs_of_nonneg (by positivity : 0 ≤ (m + b) * X)] at h3
      rw [abs_of_nonneg (by positivity : 0 ≤ m * (X * Q))] at h2
      linarith
    have hXs : X ≤ X * s := le_mul_of_one_le_right hX0 hs1
    have hT1 : Sb ≤ D * C₂ * P * (X * s) := by
      calc Sb ≤ b * (C₂ * X) := hSbC
        _ ≤ (D * P) * (C₂ * X) := by gcongr
        _ = D * C₂ * P * X := by ring
        _ ≤ D * C₂ * P * (X * s) := by gcongr
    have hT2 : (m + b) * X ≤ (1 + D) * P * (X * s) := by
      calc (m + b) * X ≤ (P + D * P) * X := by gcongr
        _ = (1 + D) * P * X := by ring
        _ ≤ (1 + D) * P * (X * s) := by gcongr
    have hT3 : m * Q * X ≤ P * (X * s) := by
      calc m * Q * X ≤ P * X := by gcongr
        _ ≤ P * (X * s) := by gcongr
    have hT4 : |E| ≤ C₁ * P * (X * s) := by
      calc |E| ≤ ρ * (C₁ * (Q ^ d * s)) := hEle
        _ ≤ (P * Q) * (C₁ * (Q ^ d * s)) := by gcongr
        _ = C₁ * P * (X * s) := by rw [hXd]; ring
    have : (2 + D + C₁ + D * C₂) * P * (X * s) = D * C₂ * P * (X * s) +
        (1 + D) * P * (X * s) + P * (X * s) + C₁ * P * (X * s) := by ring
    linarith
  have hP0 : 0 < P / 2 := by linarith
  have hmain : |N - Q ^ (d + 2)| * (P / 2) ≤
      (2 * (2 + D + C₁ + D * C₂) * (X * s)) * (P / 2) := by
    calc |N - Q ^ (d + 2)| * (P / 2) ≤ |N - Q ^ (d + 2)| * (P - 1 - m) := by gcongr
      _ = |(N - Q ^ (d + 2)) * (P - 1 - m)| := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < P - 1 - m)]
      _ ≤ (2 + D + C₁ + D * C₂) * P * (X * s) := by rw [hkey]; exact hbound
      _ = (2 * (2 + D + C₁ + D * C₂) * (X * s)) * (P / 2) := by ring
  rw [hpow2]
  exact le_of_mul_le_mul_right hmain hP0

end Estimate

end Langlands.AlgebraicGeometry.LangWeil.Slicing
