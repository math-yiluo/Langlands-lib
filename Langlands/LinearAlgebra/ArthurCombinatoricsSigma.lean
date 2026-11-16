import Langlands.LinearAlgebra.ArthurCombinatoricsAlternating
import Langlands.LinearAlgebra.ArthurCombinatoricsCartanInverse

/-!
# Arthur's characterization of `σ_{P_1}^{P_2}` and the vanishing of `∑ ± τ τ̂`

Arthur 1978, Lemma 6.1 and the remark after Corollary 6.2.

* `sigma_eq`: Lemma 6.1 inside the Levi subgroup attached to any `S ⊆ b.support`;
* `sigmaCharacterizationStatement`: the case `S = b.support`;
* `tauTauHatVanishingStatement`: the relative identity `∑ (−1)^{|Θ_P \ Θ₁|} τ_R^{Θ₁} τ̂_{Θ₁}^{Θ_P} = 0`
  for `Θ_R ⊊ Θ_P`, which is `± σ_R^R` relative to `Θ_P`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

section Sets

variable {ι : Type*} [DecidableEq ι]

/-- For `X ⊆ Y ⊆ Z`, `|Z \ X| = |Z \ Y| + |Y \ X|`. -/
theorem card_sdiff_trans {X Y Z : Finset ι} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    (Z \ X).card = (Z \ Y).card + (Y \ X).card := by
  rw [card_sdiff_of_subset (hXY.trans hYZ), card_sdiff_of_subset hYZ, card_sdiff_of_subset hXY]
  have h1 := card_le_card hXY
  have h2 := card_le_card hYZ
  omega

/-- The interval sum `∑_{A ⊆ Θ ⊆ B} (−1)^{|Θ \ A|}` is `1` if `A = B` and `0` otherwise. -/
theorem alternatingSum_eq' (A B : Finset ι) (h : A ⊆ B) :
    ∑ Θ ∈ B.powerset.filter (A ⊆ ·), (-1 : ℤ) ^ (Θ \ A).card = if A = B then 1 else 0 := by
  have hsign : ∀ Θ ∈ B.powerset.filter (A ⊆ ·),
      (-1 : ℤ) ^ (Θ \ A).card = (-1) ^ (B \ A).card * (-1) ^ (B \ Θ).card := by
    intro Θ hΘ
    rw [mem_filter, mem_powerset] at hΘ
    rw [card_sdiff_trans hΘ.2 hΘ.1, pow_add, mul_comm ((-1 : ℤ) ^ (B \ Θ).card), mul_assoc,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
  rw [sum_congr rfl hsign, ← mul_sum, alternatingSum_eq A B h]
  split_ifs with hAB
  · rw [hAB, Finset.sdiff_self, card_empty, pow_zero, mul_one]
  · rw [mul_zero]

end Sets

variable {ι M N : Type*} [DecidableEq ι] [Finite ι] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] (b : P.Base)

section Geometry

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem weightCoordinate_apply {Θ : Finset ι} {i : ι} (hi : i ∈ Θ) (Y : N) :
    weightCoordinate P Θ i Y = ∑ k : Θ, (cartanBlock P Θ)⁻¹ ⟨i, hi⟩ k * P.root' k Y := by
  simp [weightCoordinate, hi]

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem levelProjection_apply (Θ : Finset ι) (Y : N) :
    levelProjection P Θ Y = Y - ∑ j : Θ, weightCoordinate P Θ j Y • P.coroot j := by
  simp [levelProjection]

omit [DecidableEq ι] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem root'_eq_zero_of_mem_rootAnnihilator {Θ : Finset ι} {Z : N}
    (hZ : Z ∈ rootAnnihilator P Θ) {i : ι} (hi : i ∈ Θ) : P.root' i Z = 0 := by
  have := (Submodule.mem_iInf _).mp hZ i
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp this hi)

omit [DecidableEq ι] [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
theorem rootAnnihilator_anti {Θ S : Finset ι} (h : Θ ⊆ S) {Z : N}
    (hZ : Z ∈ rootAnnihilator P S) : Z ∈ rootAnnihilator P Θ := by
  simp only [rootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i hi
  exact root'_eq_zero_of_mem_rootAnnihilator hZ (h hi)

omit [P.IsCrystallographic] in
theorem root'_levelProjection_eq_zero {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (H : N) {i : ι}
    (hi : i ∈ Θ) : P.root' i (levelProjection P Θ H) = 0 :=
  root'_eq_zero_of_mem_rootAnnihilator (levelProjection_mem_rootAnnihilator b hΘ H) hi

omit [DecidableEq ι] [P.IsRootSystem] in
theorem cartanBlock_nonpos_of_ne {Θ : Finset ι} (hΘ : Θ ⊆ b.support) {k j : Θ} (h : k ≠ j) :
    cartanBlock P Θ k j ≤ 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [cartanBlock_apply, P.root'_coroot_eq_pairing]
  exact pairing_nonpos_of_ne b (fun e => h (Subtype.ext e)) (hΘ k.2) (hΘ j.2)

/-- The entries of the inverse Cartan block are nonnegative (`cartanBlock_inv_nonneg`). -/
theorem cartanBlock_inv_nonneg' {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (i k : Θ) :
    0 ≤ (cartanBlock P Θ)⁻¹ i k := by
  have : Fintype ι := Fintype.ofFinite ι
  exact cartanBlock_inv_nonneg b hΘ i k

/-- The diagonal entries of the inverse Cartan block are at least `1/2`. -/
theorem half_le_cartanBlock_inv_self {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (k : Θ) :
    1 / 2 ≤ (cartanBlock P Θ)⁻¹ k k := by
  have hinv := Matrix.nonsing_inv_mul (cartanBlock P Θ) (isUnit_det_cartanBlock b hΘ)
  have h := congrFun (congrFun hinv k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← add_sum_erase _ _ (mem_univ k)] at h
  have hkk : cartanBlock P Θ k k = 2 := by
    rw [cartanBlock_apply, P.root'_coroot_eq_pairing, P.pairing_same]
  have hrest : ∑ l ∈ univ.erase k, (cartanBlock P Θ)⁻¹ k l * cartanBlock P Θ l k ≤ 0 :=
    sum_nonpos fun l hl => mul_nonpos_of_nonneg_of_nonpos (cartanBlock_inv_nonneg' b hΘ k l)
      (cartanBlock_nonpos_of_ne b hΘ (ne_of_mem_erase hl))
  rw [hkk] at h
  linarith

/-- If the simple roots of `Θ` are nonnegative on `Y` and `α_k(Y) > 0`, then `ϖ_k(Y) > 0`. -/
theorem weightCoordinate_pos {Θ : Finset ι} (hΘ : Θ ⊆ b.support) {k : ι} (hk : k ∈ Θ) {Y : N}
    (h0 : ∀ i ∈ Θ, 0 ≤ P.root' i Y) (hpos : 0 < P.root' k Y) :
    0 < weightCoordinate P Θ k Y := by
  rw [weightCoordinate_apply hk]
  have hterm : ∀ l : Θ, 0 ≤ (cartanBlock P Θ)⁻¹ ⟨k, hk⟩ l * P.root' l Y := fun l =>
    mul_nonneg (cartanBlock_inv_nonneg' b hΘ _ l) (h0 l l.2)
  have hkk : 0 < (cartanBlock P Θ)⁻¹ ⟨k, hk⟩ ⟨k, hk⟩ * P.root' k Y :=
    mul_pos (lt_of_lt_of_le (by norm_num) (half_le_cartanBlock_inv_self b hΘ _)) hpos
  exact lt_of_lt_of_le hkk
    (single_le_sum (f := fun l : Θ => (cartanBlock P Θ)⁻¹ ⟨k, hk⟩ l * P.root' l Y)
      (fun l _ => hterm l) (mem_univ (⟨k, hk⟩ : Θ)))

/-- If the simple roots of `Θ` are nonpositive on `Y`, then so is every `ϖ_k`, `k ∈ Θ`. -/
theorem weightCoordinate_nonpos {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (k : ι) {Y : N}
    (h0 : ∀ i ∈ Θ, P.root' i Y ≤ 0) : weightCoordinate P Θ k Y ≤ 0 := by
  by_cases hk : k ∈ Θ
  · rw [weightCoordinate_apply hk]
    exact sum_nonpos fun l _ =>
      mul_nonpos_of_nonneg_of_nonpos (cartanBlock_inv_nonneg' b hΘ _ l) (h0 l l.2)
  · simp [weightCoordinate, hk]

/-- For `k ∈ Θ` and a simple root `j ∉ Θ`, `ϖ^Θ_k(α_j^∨) ≤ 0`. -/
theorem weightCoordinate_coroot_nonpos {Θ : Finset ι} (hΘ : Θ ⊆ b.support) (k : ι) {j : ι}
    (hj : j ∈ b.support) (hjΘ : j ∉ Θ) : weightCoordinate P Θ k (P.coroot j) ≤ 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  refine weightCoordinate_nonpos b hΘ k fun i hi => ?_
  rw [P.root'_coroot_eq_pairing]
  exact pairing_nonpos_of_ne b (fun e => hjΘ (e ▸ hi)) (hΘ hi) hj

omit [P.IsCrystallographic] in
/-- Expansion of `ϖ^Θ_k` in the weights `ϖ^S_j` of a larger `S`. -/
theorem weightCoordinate_eq_sum_of_subset {Θ S : Finset ι} (hΘS : Θ ⊆ S) (hS : S ⊆ b.support)
    (k : ι) (Y : N) :
    weightCoordinate P Θ k Y =
      ∑ j : S, weightCoordinate P S j Y * weightCoordinate P Θ k (P.coroot j) := by
  have hY : Y = levelProjection P S Y + ∑ j : S, weightCoordinate P S j Y • P.coroot j := by
    rw [levelProjection_apply]; abel
  have hlp : weightCoordinate P Θ k (levelProjection P S Y) = 0 :=
    weightCoordinate_eq_zero_of_mem_rootAnnihilator k
      (rootAnnihilator_anti hΘS (levelProjection_mem_rootAnnihilator b hS Y))
  conv_lhs => rw [hY]
  rw [map_add, hlp, zero_add, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- **Comparison of weights.** For `Θ ⊆ S` and `k ∈ Θ`, if `ϖ^S_j(Y) ≥ 0` for every
`j ∈ S \ Θ`, then `ϖ^Θ_k(Y) ≤ ϖ^S_k(Y)`. -/
theorem weightCoordinate_le_of_subset {Θ S : Finset ι} (hΘS : Θ ⊆ S) (hS : S ⊆ b.support)
    {k : ι} (hk : k ∈ Θ) {Y : N} (hY : ∀ j ∈ S \ Θ, 0 ≤ weightCoordinate P S j Y) :
    weightCoordinate P Θ k Y ≤ weightCoordinate P S k Y := by
  rw [weightCoordinate_eq_sum_of_subset b hΘS hS k Y]
  have hkS : k ∈ S := hΘS hk
  have hle : ∀ j : S, weightCoordinate P S j Y * weightCoordinate P Θ k (P.coroot j) ≤
      if (j : ι) = k then weightCoordinate P S j Y else 0 := by
    intro j
    by_cases hjΘ : (j : ι) ∈ Θ
    · rw [weightCoordinate_coroot b (hΘS.trans hS) hk hjΘ]
      by_cases hjk : (j : ι) = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · have hjk : (j : ι) ≠ k := fun e => hjΘ (e ▸ hk)
      rw [ite_eq_right hjk]
      exact mul_nonpos_of_nonneg_of_nonpos (hY j (mem_sdiff.mpr ⟨j.2, hjΘ⟩))
        (weightCoordinate_coroot_nonpos b (hΘS.trans hS) k (hS j.2) hjΘ)
  refine (sum_le_sum fun j _ => hle j).trans (le_of_eq ?_)
  rw [sum_eq_single (⟨k, hkS⟩ : S)]
  · simp
  · intro j _ hj
    rw [ite_eq_right fun e => hj (Subtype.ext e)]
  · intro h; exact absurd (mem_univ _) h

omit [P.IsCrystallographic] in
/-- For `Θ ⊆ S ⊆ b.support` and `k ∈ S \ Θ`, `ϖ^S_k(H_P) = ϖ^S_k(H)`, `H_P` the projection
attached to `Θ`. -/
theorem weightCoordinate_levelProjection {Θ S : Finset ι} (hΘS : Θ ⊆ S) (hS : S ⊆ b.support)
    {k : ι} (hk : k ∈ S) (hkΘ : k ∉ Θ) (H : N) :
    weightCoordinate P S k (levelProjection P Θ H) = weightCoordinate P S k H := by
  rw [levelProjection_apply, map_sub, map_sum]
  have : ∀ j : Θ, weightCoordinate P S k (weightCoordinate P Θ j H • P.coroot j) = 0 := by
    intro j
    rw [map_smul, weightCoordinate_coroot b hS hk (hΘS j.2), ite_eq_right fun e : k = (j : ι) => hkΘ (e ▸ j.2),
      smul_zero]
  simp [this]

end Geometry

section Sigma

variable {b}

/-- **Arthur 1978, Lemma 6.1**, inside the Levi subgroup attached to `S ⊆ b.support`:
`σ_{P_1}^{P_2}(H)` is `1` exactly when (i) `α_i(H_{P_1}) > 0` for `i ∈ Θ₂ \ Θ₁`,
(ii) `α_i(H_{P_1}) ≤ 0` for `i ∈ S \ Θ₂` and (iii) `ϖ^S_i(H) > 0` for `i ∈ S \ Θ₂`, and `0`
otherwise. -/
theorem sigma_eq {S Θ₁ Θ₂ : Finset ι} (h12 : Θ₁ ⊆ Θ₂) (h2S : Θ₂ ⊆ S) (hS : S ⊆ b.support)
    (H : N) :
    sigma P S Θ₁ Θ₂ H =
      if (∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i (levelProjection P Θ₁ H)) ∧
          (∀ i ∈ S \ Θ₂, P.root' i (levelProjection P Θ₁ H) ≤ 0) ∧
          (∀ i ∈ S \ Θ₂, 0 < weightCoordinate P S i H) then 1 else 0 := by
  classical
  set H₁ := levelProjection P Θ₁ H with hH₁
  set R := S.filter fun i => weightCoordinate P S i H ≤ 0 with hR
  set A := Θ₂ ∪ R with hA
  set B := S.filter fun i => i ∈ Θ₁ ∨ 0 < P.root' i H₁ with hB
  have h1S : Θ₁ ⊆ S := h12.trans h2S
  have hRS : R ⊆ S := filter_subset _ _
  have hAS : A ⊆ S := union_subset h2S hRS
  have h2A : Θ₂ ⊆ A := subset_union_left
  -- the two characteristic functions
  have htau : ∀ Θ₃, Θ₂ ⊆ Θ₃ → Θ₃ ⊆ S → (tau P Θ₁ Θ₃ H = if Θ₃ ⊆ B then 1 else 0) := by
    intro Θ₃ h23 h3S
    unfold tau
    congr 1
    refine propext ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · refine mem_filter.mpr ⟨h3S hi, ?_⟩
      by_cases hi1 : i ∈ Θ₁
      · exact Or.inl hi1
      · exact Or.inr (h i (mem_sdiff.mpr ⟨hi, hi1⟩))
    · obtain ⟨hi3, hi1⟩ := mem_sdiff.mp hi
      exact ((mem_filter.mp (h hi3)).2.resolve_left hi1)
  have htauHat : ∀ Θ₃, Θ₂ ⊆ Θ₃ → Θ₃ ⊆ S → (tauHat P Θ₃ S H = if A ⊆ Θ₃ then 1 else 0) := by
    intro Θ₃ h23 h3S
    unfold tauHat
    congr 1
    refine propext ⟨fun h => union_subset h23 fun i hi => ?_, fun h i hi => ?_⟩
    · obtain ⟨hiS, hle⟩ := mem_filter.mp hi
      by_contra hi3
      exact absurd (h i (mem_sdiff.mpr ⟨hiS, hi3⟩)) (not_lt.mpr hle)
    · obtain ⟨hiS, hi3⟩ := mem_sdiff.mp hi
      by_contra hle
      exact hi3 (h (mem_union_right _ (mem_filter.mpr ⟨hiS, not_lt.mp hle⟩)))
  -- `σ` as an interval sum
  have hsig : sigma P S Θ₁ Θ₂ H =
      ∑ Θ₃ ∈ B.powerset.filter (A ⊆ ·), (-1 : ℤ) ^ (Θ₃ \ Θ₂).card := by
    unfold sigma
    have hterm : ∀ Θ₃ ∈ S.powerset.filter (Θ₂ ⊆ ·),
        (-1 : ℤ) ^ (Θ₃ \ Θ₂).card * tau P Θ₁ Θ₃ H * tauHat P Θ₃ S H =
          if A ⊆ Θ₃ ∧ Θ₃ ⊆ B then (-1 : ℤ) ^ (Θ₃ \ Θ₂).card else 0 := by
      intro Θ₃ hΘ₃
      rw [mem_filter, mem_powerset] at hΘ₃
      rw [htau Θ₃ hΘ₃.2 hΘ₃.1, htauHat Θ₃ hΘ₃.2 hΘ₃.1]
      by_cases hb : Θ₃ ⊆ B <;> by_cases ha : A ⊆ Θ₃ <;> simp [ha, hb]
    rw [sum_congr rfl hterm, ← sum_filter, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext Θ₃
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨-, -, hA3, h3B⟩; exact ⟨h3B, hA3⟩
    · rintro ⟨h3B, hA3⟩
      exact ⟨h3B.trans (filter_subset _ _), h2A.trans hA3, hA3, h3B⟩
  -- the conditions of the lemma
  have hcond : ((∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i H₁) ∧ (∀ i ∈ S \ Θ₂, P.root' i H₁ ≤ 0) ∧
      (∀ i ∈ S \ Θ₂, 0 < weightCoordinate P S i H)) ↔ (B = Θ₂ ∧ A = Θ₂) := by
    constructor
    · rintro ⟨hi, hii, hiii⟩
      refine ⟨Subset.antisymm (fun i hiB => ?_) (fun i hi2 => ?_), Subset.antisymm
        (union_subset (subset_refl _) fun i hiR => ?_) h2A⟩
      · obtain ⟨hiS, hor⟩ := mem_filter.mp hiB
        by_contra hi2
        rcases hor with h1 | hpos
        · exact hi2 (h12 h1)
        · exact absurd (hii i (mem_sdiff.mpr ⟨hiS, hi2⟩)) (not_le.mpr hpos)
      · refine mem_filter.mpr ⟨h2S hi2, ?_⟩
        by_cases hi1 : i ∈ Θ₁
        · exact Or.inl hi1
        · exact Or.inr (hi i (mem_sdiff.mpr ⟨hi2, hi1⟩))
      · obtain ⟨hiS, hle⟩ := mem_filter.mp hiR
        by_contra hi2
        exact absurd (hiii i (mem_sdiff.mpr ⟨hiS, hi2⟩)) (not_lt.mpr hle)
    · rintro ⟨hB2, hA2⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
      · obtain ⟨hi2, hi1⟩ := mem_sdiff.mp hi
        rw [← hB2] at hi2
        exact (mem_filter.mp hi2).2.resolve_left hi1
      · obtain ⟨hiS, hi2⟩ := mem_sdiff.mp hi
        by_contra hpos
        rw [not_le] at hpos
        exact hi2 (hB2 ▸ mem_filter.mpr ⟨hiS, Or.inr hpos⟩)
      · obtain ⟨hiS, hi2⟩ := mem_sdiff.mp hi
        by_contra hle
        rw [not_lt] at hle
        exact hi2 (hA2 ▸ mem_union_right _ (mem_filter.mpr ⟨hiS, hle⟩))
  -- the geometric step: `A = B` forces `A = Θ₂`
  have hgeom : A = B → A = Θ₂ := by
    intro hAB
    refine Subset.antisymm (fun k hkA => ?_) h2A
    by_contra hk2
    have hkR : k ∈ R := (mem_union.mp hkA).resolve_left hk2
    obtain ⟨hkS, hkle⟩ := mem_filter.mp hkR
    have hk1 : k ∉ Θ₁ := fun h => hk2 (h12 h)
    have hkpos : 0 < P.root' k H₁ := (mem_filter.mp (hAB ▸ hkA)).2.resolve_left hk1
    -- the simple roots of `A` are nonnegative on `H₁`
    have hA0 : ∀ i ∈ A, 0 ≤ P.root' i H₁ := by
      intro i hiA
      rcases (mem_filter.mp (hAB ▸ hiA)).2 with hi1 | hpos
      · exact (root'_levelProjection_eq_zero b (h1S.trans hS) H hi1).ge
      · exact hpos.le
    have hwA : 0 < weightCoordinate P A k H₁ :=
      weightCoordinate_pos b (hAS.trans hS) hkA hA0 hkpos
    -- the weights `ϖ^S_j`, `j ∈ S \ A`, are positive on `H₁`
    have hout : ∀ j ∈ S \ A, 0 ≤ weightCoordinate P S j H₁ := by
      intro j hj
      obtain ⟨hjS, hjA⟩ := mem_sdiff.mp hj
      have hj1 : j ∉ Θ₁ := fun h => hjA (h2A (h12 h))
      rw [hH₁, weightCoordinate_levelProjection b h1S hS hjS hj1]
      by_contra hneg
      exact hjA (mem_union_right _ (mem_filter.mpr ⟨hjS, (not_le.mp hneg).le⟩))
    have hwS := weightCoordinate_le_of_subset b hAS hS hkA hout
    rw [hH₁, weightCoordinate_levelProjection b h1S hS hkS hk1] at hwS
    exact absurd (lt_of_lt_of_le hwA hwS) (not_lt.mpr hkle)
  rw [hsig]
  by_cases hAB : A ⊆ B
  · have hrw : ∀ Θ₃ ∈ B.powerset.filter (A ⊆ ·),
        (-1 : ℤ) ^ (Θ₃ \ Θ₂).card = (-1) ^ (A \ Θ₂).card * (-1) ^ (Θ₃ \ A).card := by
      intro Θ₃ hΘ₃
      rw [mem_filter, mem_powerset] at hΘ₃
      rw [card_sdiff_trans h2A hΘ₃.2, pow_add, mul_comm]
    rw [sum_congr rfl hrw, ← mul_sum, alternatingSum_eq' A B hAB]
    by_cases hc : (∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i H₁) ∧ (∀ i ∈ S \ Θ₂, P.root' i H₁ ≤ 0) ∧
        (∀ i ∈ S \ Θ₂, 0 < weightCoordinate P S i H)
    · obtain ⟨hB2, hA2⟩ := hcond.mp hc
      rw [ite_eq_left hc, ite_eq_left (hA2.trans hB2.symm), hA2, Finset.sdiff_self, card_empty, pow_zero,
        mul_one]
    · rw [ite_eq_right hc]
      by_cases he : A = B
      · exact absurd (hcond.mpr ⟨(hgeom he) ▸ he.symm, hgeom he⟩) hc
      · rw [ite_eq_right he, mul_zero]
  · have hempty : ∀ Θ₃ ∈ B.powerset.filter (A ⊆ ·), (-1 : ℤ) ^ (Θ₃ \ Θ₂).card = 0 := by
      intro Θ₃ hΘ₃
      rw [mem_filter, mem_powerset] at hΘ₃
      exact absurd (hΘ₃.2.trans hΘ₃.1) hAB
    rw [sum_congr rfl hempty, sum_const_zero]
    by_cases hc : (∀ i ∈ Θ₂ \ Θ₁, 0 < P.root' i H₁) ∧ (∀ i ∈ S \ Θ₂, P.root' i H₁ ≤ 0) ∧
        (∀ i ∈ S \ Θ₂, 0 < weightCoordinate P S i H)
    · obtain ⟨hB2, hA2⟩ := hcond.mp hc
      exact absurd (hA2.trans hB2.symm).subset hAB
    · rw [ite_eq_right hc]

end Sigma

/-- **Arthur 1978, Lemma 6.1.** -/
theorem sigmaCharacterizationStatement : SigmaCharacterizationStatement.{u} := by
  intro ι M N _ _ _ _ _ _ P _ _ b Θ₁ Θ₂ h12 h2 H
  exact sigma_eq h12 h2 subset_rfl H

omit [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] in
/-- `∑_{R ⊆ P_1 ⊆ P} (−1)^{|Θ_P \ Θ₁|} τ_R^{P_1}(H) τ̂_{P_1}^P(H) = (−1)^{|Θ_P \ Θ_R|} σ_R^R(H)`,
`σ` taken relative to `Θ_P`. -/
theorem tauTauHat_sum_eq_sigma (ΘR ΘP : Finset ι) (H : N) :
    ∑ Θ₁ ∈ ΘP.powerset.filter (ΘR ⊆ ·),
        (-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H =
      (-1) ^ (ΘP \ ΘR).card * sigma P ΘP ΘR ΘR H := by
  unfold sigma
  rw [mul_sum]
  refine sum_congr rfl fun Θ₁ hΘ₁ => ?_
  rw [mem_filter, mem_powerset] at hΘ₁
  rw [card_sdiff_trans hΘ₁.2 hΘ₁.1, pow_add]
  have hsq : (-1 : ℤ) ^ (Θ₁ \ ΘR).card * (-1) ^ (Θ₁ \ ΘR).card = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc (-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H
      = (-1 : ℤ) ^ (ΘP \ Θ₁).card * ((-1) ^ (Θ₁ \ ΘR).card * (-1) ^ (Θ₁ \ ΘR).card) *
          tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H := by rw [hsq, mul_one]
    _ = (-1) ^ (ΘP \ Θ₁).card * (-1) ^ (Θ₁ \ ΘR).card *
          ((-1) ^ (Θ₁ \ ΘR).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H) := by ring

/-- `σ_R^R(H) = 0` relative to `Θ_P ⊋ Θ_R`: conditions (ii) and (iii) of Lemma 6.1 contradict each
other, since each weight is a nonnegative combination of the simple roots. -/
theorem sigma_self_eq_zero {ΘR ΘP : Finset ι} (hRP : ΘR ⊆ ΘP) (hP : ΘP ⊆ b.support)
    (hne : ΘR ≠ ΘP) (H : N) : sigma P ΘP ΘR ΘR H = 0 := by
  rw [sigma_eq subset_rfl hRP hP, ite_eq_right]
  rintro ⟨-, hii, hiii⟩
  obtain ⟨k, hk⟩ : (ΘP \ ΘR).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
    exact fun h => hne (Subset.antisymm hRP h)
  obtain ⟨hkP, hkR⟩ := mem_sdiff.mp hk
  have hle : weightCoordinate P ΘP k (levelProjection P ΘR H) ≤ 0 := by
    refine weightCoordinate_nonpos b hP k fun i hi => ?_
    by_cases hiR : i ∈ ΘR
    · exact (root'_levelProjection_eq_zero b (hRP.trans hP) H hiR).le
    · exact hii i (mem_sdiff.mpr ⟨hi, hiR⟩)
  rw [weightCoordinate_levelProjection b hRP hP hkP hkR] at hle
  exact absurd (hiii k hk) (not_lt.mpr hle)

/-- **The remark after Arthur 1978, Corollary 6.2**, in relative form. -/
theorem tauTauHatVanishingStatement : TauTauHatVanishingStatement.{u} := by
  intro ι M N _ _ _ _ _ _ P _ _ b ΘR ΘP hRP hP hne H
  rw [tauTauHat_sum_eq_sigma ΘR ΘP H, sigma_self_eq_zero (b := b) hRP hP hne H, mul_zero]

end Langlands.ArthurCombinatorics
