import Langlands.LinearAlgebra.ArthurCombinatoricsLanglandsLemma
import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport

/-! # The combinatorics of Arthur's partition lemma

Arthur 1978, proof of Lemma 6.4 (pp.941–942). For a crystallographic root system over `ℝ` with a
base `b` and `Θ_Q ⊆ Θ_P ⊆ b.support`:

* `existsUnique_weight_nonpos_tau`: for every `H` there is exactly one `Θ_R` with
  `Θ_Q ⊆ Θ_R ⊆ Θ_P`, `ϖ^R_i(H) ≤ 0` for `i ∈ Θ_R \ Θ_Q` and `τ_R^P(H) = 1` (Langlands'
  combinatorial lemma, Lemma 6.3, with `Λ` the sum of the fundamental weights);
* `root'_pos_of_weight_nonpos_of_tau`: if `ϖ^{P_1}_j(H) ≤ 0` for `j ∈ Θ_1` and
  `τ_{P_1}^P(H) = 1`, then `α_i(H) > 0` for every `i ∈ Θ_P \ Θ_1`;
* `eq_of_weight_nonpos_of_tau`: two pairs `(Θ_1, H_1)`, `(Θ_2, H_2)` with these properties and
  `H_2 − H_1` in the coroot span of `Θ_1 ∩ Θ_2` have `Θ_1 = Θ_2`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

variable {ι M N : Type*} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] (b : P.Base)

/-- The sum `∑_k ϖ_k` of the fundamental weights of `b`, as an element of the weight space. -/
def weightSum : M :=
  ∑ k : b.support, ∑ l : b.support, (cartanBlock P b.support)⁻¹ k l • P.root (l : ι)

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem toLinearMap_weightSum (H : N) :
    P.toLinearMap (weightSum b) H = ∑ k : b.support, weightCoordinate P b.support k H := by
  unfold weightSum
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weightCoordinate_apply k.2]

omit [P.IsCrystallographic] in
theorem toLinearMap_weightSum_coroot {j : ι} (hj : j ∈ b.support) :
    P.toLinearMap (weightSum b) (P.coroot j) = 1 := by
  rw [toLinearMap_weightSum]
  rw [Finset.sum_eq_single (⟨j, hj⟩ : b.support)]
  · rw [weightCoordinate_coroot b subset_rfl hj hj, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · intro k _ hk
    rw [weightCoordinate_coroot b subset_rfl k.2 hj,
      ite_eq_right_of_eq_false _ _ (eq_false fun e => hk (Subtype.ext e))]
  · intro h
    exact absurd (mem_univ _) h

/-- For `i ∈ b.support \ Θ_Q`, `Λ(α_i^∨) > 0` for `Λ = weightSum b`, the coroot being projected
to `𝔞_Q`. -/
theorem corootValue_weightSum_pos {ΘQ : Finset ι} (hQ : ΘQ ⊆ b.support) {i : ι}
    (hi : i ∈ b.support) (hiQ : i ∉ ΘQ) : 0 < corootValue P ΘQ (weightSum b) i := by
  unfold corootValue
  rw [levelProjection_apply, map_sub, map_sum, toLinearMap_weightSum_coroot b hi]
  have hterm : ∀ j : ΘQ, P.toLinearMap (weightSum b)
      (weightCoordinate P ΘQ j (P.coroot i) • P.coroot j) =
        weightCoordinate P ΘQ j (P.coroot i) := by
    intro j
    rw [map_smul, smul_eq_mul, toLinearMap_weightSum_coroot b (hQ j.2), mul_one]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  have hle : ∑ j : ΘQ, weightCoordinate P ΘQ j (P.coroot i) ≤ 0 :=
    sum_nonpos fun j _ => weightCoordinate_coroot_nonpos b hQ j hi hiQ
  linarith

/-- **Langlands' combinatorial lemma, in the form used for Arthur's partition** (Arthur 1978,
Lemma 6.3 with `Λ` in the positive chamber): for every `H` there is exactly one `Θ_R` with
`Θ_Q ⊆ Θ_R ⊆ Θ_P`, `ϖ^R_i(H) ≤ 0` for every `i ∈ Θ_R \ Θ_Q` and `τ_R^P(H) = 1`. -/
theorem existsUnique_weight_nonpos_tau {ΘQ ΘP : Finset ι} (hQP : ΘQ ⊆ ΘP)
    (hP : ΘP ⊆ b.support) (H : N) :
    ∃! ΘR : Finset ι, (ΘQ ⊆ ΘR ∧ ΘR ⊆ ΘP) ∧
      (∀ i ∈ ΘR \ ΘQ, weightCoordinate P ΘR i H ≤ 0) ∧ tau P ΘR ΘP H = 1 := by
  classical
  set Λ := weightSum b with hΛ
  have hpos : ∀ i ∈ ΘP \ ΘQ, 0 < corootValue P ΘQ Λ i := fun i hi =>
    corootValue_weightSum_pos b (hQP.trans hP) (hP (mem_sdiff.mp hi).1) (mem_sdiff.mp hi).2
  have hL := langlandsCombinatorial_eq (b := b) ΘQ Λ H ΘP hQP hP
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by
    rintro ⟨i, hi, hle⟩
    exact absurd (hpos i hi) (not_lt.mpr hle)))] at hL
  set I := ΘP.powerset.filter (ΘQ ⊆ ·) with hI
  let cond : Finset ι → Prop := fun ΘR =>
    (∀ i ∈ ΘR \ ΘQ, weightCoordinate P ΘR i H ≤ 0) ∧ tau P ΘR ΘP H = 1
  have hterm : ∀ ΘR ∈ I, epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR ΘP H =
      if cond ΘR then 1 else 0 := by
    intro ΘR hR
    rw [hI, mem_filter, mem_powerset] at hR
    have hsub : ∀ i ∈ ΘR \ ΘQ, 0 < corootValue P ΘQ Λ i := fun i hi =>
      hpos i (mem_sdiff.mpr ⟨hR.1 (mem_sdiff.mp hi).1, (mem_sdiff.mp hi).2⟩)
    have heps : epsilon P ΘQ ΘR Λ = 1 := by
      unfold epsilon
      rw [Finset.filter_false_of_mem (fun i hi => not_le.mpr (hsub i hi)), card_empty,
        pow_zero]
    have hphi : phi P ΘQ ΘR Λ H =
        if ∀ i ∈ ΘR \ ΘQ, weightCoordinate P ΘR i H ≤ 0 then 1 else 0 := by
      unfold phi
      congr 1
      apply propext
      constructor
      · intro h i hi
        exact (h i hi).2 (hsub i hi)
      · intro h i hi
        exact ⟨fun hle => absurd (hsub i hi) (not_lt.mpr hle), fun _ => h i hi⟩
    have htau : tau P ΘR ΘP H = 0 ∨ tau P ΘR ΘP H = 1 := by
      unfold tau
      split_ifs <;> simp
    rw [heps, one_mul, hphi]
    by_cases hw : ∀ i ∈ ΘR \ ΘQ, weightCoordinate P ΘR i H ≤ 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hw), one_mul]
      rcases htau with h0 | h1
      · have hc : ¬ cond ΘR := fun h => absurd (h.2.symm.trans h0) (by norm_num)
        rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
        exact h0
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (⟨hw, h1⟩ : cond ΘR))]
        exact h1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hw), zero_mul,
        ite_eq_right_of_eq_false _ _ (eq_false fun h : cond ΘR => hw h.1)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole] at hL
  have hcard : (I.filter cond).card = 1 := by exact_mod_cast hL
  obtain ⟨ΘR, hR⟩ := Finset.card_eq_one.mp hcard
  have hmem : ΘR ∈ I.filter cond := by rw [hR]; exact mem_singleton_self _
  rw [mem_filter, hI, mem_filter, mem_powerset] at hmem
  refine ⟨ΘR, ⟨⟨hmem.1.2, hmem.1.1⟩, hmem.2⟩, ?_⟩
  rintro Θ' ⟨⟨hQ', hP'⟩, hc'⟩
  have h' : Θ' ∈ I.filter cond := by
    rw [mem_filter, hI, mem_filter, mem_powerset]
    exact ⟨⟨hP', hQ'⟩, hc'⟩
  rw [hR] at h'
  exact mem_singleton.mp h'

omit [P.IsRootSystem] in
/-- **Arthur 1978, proof of Lemma 6.4.** If `ϖ^{P_1}_j(H) ≤ 0` for every `j ∈ Θ_1` and
`τ_{P_1}^P(H) = 1`, then `α_i(H) > 0` for every `i ∈ Θ_P \ Θ_1`. -/
theorem root'_pos_of_weight_nonpos_of_tau {Θ₁ ΘP : Finset ι} (h1P : Θ₁ ⊆ ΘP)
    (hP : ΘP ⊆ b.support) {H : N} (hw : ∀ j ∈ Θ₁, weightCoordinate P Θ₁ j H ≤ 0)
    (ht : tau P Θ₁ ΘP H = 1) {i : ι} (hi : i ∈ ΘP) (hi1 : i ∉ Θ₁) : 0 < P.root' i H := by
  have : Fintype ι := Fintype.ofFinite ι
  have htau : 0 < P.root' i (levelProjection P Θ₁ H) := by
    unfold tau at ht
    split_ifs at ht with h
    · exact h i (mem_sdiff.mpr ⟨hi, hi1⟩)
    · exact absurd ht (by norm_num)
  have hH : P.root' i H = P.root' i (levelProjection P Θ₁ H) +
      ∑ j : Θ₁, weightCoordinate P Θ₁ j H * P.pairing i j := by
    rw [levelProjection_apply, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul, P.root'_coroot_eq_pairing]
    ring
  have hsum : 0 ≤ ∑ j : Θ₁, weightCoordinate P Θ₁ j H * P.pairing i j :=
    sum_nonneg fun j _ => mul_nonneg_of_nonpos_of_nonpos (hw j j.2)
      (pairing_nonpos_of_ne b (fun e => hi1 (e ▸ j.2)) (hP hi) (hP (h1P j.2)))
  rw [hH]
  linarith

omit [P.IsCrystallographic] in
/-- `H ↦ H_P` vanishes on `𝔞_0^P = corootSpan P Θ`. -/
theorem levelProjection_eq_zero_of_mem_corootSpan {Θ : Finset ι} (hΘ : Θ ⊆ b.support) {Z : N}
    (hZ : Z ∈ corootSpan P Θ) : levelProjection P Θ Z = 0 := by
  have h1 : levelProjection P Θ Z ∈ corootSpan P Θ := by
    have := sub_levelProjection_mem_corootSpan (P := P) Θ Z
    have h2 : levelProjection P Θ Z = Z - (Z - levelProjection P Θ Z) := by abel
    rw [h2]
    exact Submodule.sub_mem _ hZ this
  exact (Submodule.disjoint_def.mp (isCompl_corootSpan_rootAnnihilator b hΘ).disjoint) _ h1
    (levelProjection_mem_rootAnnihilator b hΘ Z)

omit [P.IsCrystallographic] in
/-- `τ_R^P` is unchanged by adding a vector of `𝔞_0^R`. -/
theorem tau_add_of_mem_corootSpan {ΘR : Finset ι} (hR : ΘR ⊆ b.support) (ΘP : Finset ι)
    (H : N) {Z : N} (hZ : Z ∈ corootSpan P ΘR) : tau P ΘR ΘP (H + Z) = tau P ΘR ΘP H := by
  unfold tau
  rw [map_add, levelProjection_eq_zero_of_mem_corootSpan b hR hZ, add_zero]

omit [DecidableEq ι] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem corootSpan_mono {Θ Θ' : Finset ι} (h : Θ ⊆ Θ') :
    corootSpan P Θ ≤ corootSpan P Θ' :=
  Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr h))

/-- **Arthur 1978, proof of Lemma 6.4, "at most one".** Let `Θ_1, Θ_2 ⊆ Θ_P` and `H_1, H_2` with
`ϖ^{P_a}_j(H_a) ≤ 0` for `j ∈ Θ_a` and `τ_{P_a}^P(H_a) = 1` (`a = 1, 2`). If `H_2 − H_1` lies in
the coroot span of `Θ_1 ∩ Θ_2`, then `Θ_1 = Θ_2`. -/
theorem eq_of_weight_nonpos_of_tau {Θ₁ Θ₂ ΘP : Finset ι} (h1P : Θ₁ ⊆ ΘP) (h2P : Θ₂ ⊆ ΘP)
    (hP : ΘP ⊆ b.support) {H₁ H₂ : N} (hZ : H₂ - H₁ ∈ corootSpan P (Θ₁ ∩ Θ₂))
    (hw₁ : ∀ j ∈ Θ₁, weightCoordinate P Θ₁ j H₁ ≤ 0) (ht₁ : tau P Θ₁ ΘP H₁ = 1)
    (hw₂ : ∀ j ∈ Θ₂, weightCoordinate P Θ₂ j H₂ ≤ 0) (ht₂ : tau P Θ₂ ΘP H₂ = 1) :
    Θ₁ = Θ₂ := by
  have hQP : Θ₁ ∩ Θ₂ ⊆ ΘP := inter_subset_left.trans h1P
  obtain ⟨ΘR, -, huniq⟩ := existsUnique_weight_nonpos_tau b hQP hP H₁
  have hZ' : H₁ - H₂ ∈ corootSpan P (Θ₁ ∩ Θ₂) := by
    have := Submodule.neg_mem _ hZ
    rwa [neg_sub] at this
  have hH₁ : H₁ = H₂ + (H₁ - H₂) := by abel
  have h1 := huniq Θ₁ ⟨⟨inter_subset_left, h1P⟩, fun i hi => hw₁ i (mem_sdiff.mp hi).1, ht₁⟩
  have h2 := huniq Θ₂ ⟨⟨inter_subset_right, h2P⟩, fun i hi => by
      rw [hH₁, map_add, weightCoordinate_eq_zero_of_mem_corootSpan b inter_subset_right
        (h2P.trans hP) (mem_sdiff.mp hi).1
        (fun h => (mem_sdiff.mp hi).2 h) hZ', add_zero]
      exact hw₂ i (mem_sdiff.mp hi).1, by
      rw [hH₁, tau_add_of_mem_corootSpan b (h2P.trans hP) ΘP H₂
        (corootSpan_mono inter_subset_right hZ')]
      exact ht₂⟩
  rw [h1, h2]

omit [P.IsCrystallographic] in
/-- `𝔞_0^{P_1} ∩ 𝔞_0^{P_2} = 𝔞_0^{P_1 ∩ P_2}`: the coroot spans of two subsets of a base meet in
the coroot span of their intersection. -/
theorem mem_corootSpan_inter {Θ₁ Θ₂ : Finset ι} (h1 : Θ₁ ⊆ b.support) (h2 : Θ₂ ⊆ b.support)
    {Z : N} (hZ1 : Z ∈ corootSpan P Θ₁) (hZ2 : Z ∈ corootSpan P Θ₂) :
    Z ∈ corootSpan P (Θ₁ ∩ Θ₂) := by
  have hZS : Z ∈ corootSpan P b.support := corootSpan_mono h1 hZ1
  have hZ : Z = ∑ j : b.support, weightCoordinate P b.support j Z • P.coroot j := by
    have h0 := levelProjection_eq_zero_of_mem_corootSpan b subset_rfl hZS
    rw [levelProjection_apply, sub_eq_zero] at h0
    exact h0
  rw [hZ]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : (j : ι) ∈ Θ₁ ∩ Θ₂
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · have hw : weightCoordinate P b.support j Z = 0 := by
      rcases not_and_or.mp (fun h => hj (mem_inter.mpr h)) with hj1 | hj2
      · exact weightCoordinate_eq_zero_of_mem_corootSpan b h1 subset_rfl j.2 hj1 hZ1
      · exact weightCoordinate_eq_zero_of_mem_corootSpan b h2 subset_rfl j.2 hj2 hZ2
    rw [hw, zero_smul]
    exact Submodule.zero_mem _

end Langlands.ArthurCombinatorics
