import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-!
# Langlands' combinatorial lemma

Arthur 1978, Lemma 6.3: for `Θ_Q ⊆ Θ_P ⊆ b.support`,
`∑_{Θ_Q ⊆ Θ_R ⊆ Θ_P} ε_Q^R(Λ) φ_Q^R(Λ, H) τ_R^P(H)` is `0` if `Λ(α^∨) ≤ 0` for some
`α ∈ Δ_Q^P`, and `1` otherwise.

* `tau_eq_neg_sum`: for `Θ_R ⊊ Θ_P`, `τ_R^P = −∑_{Θ_R ⊆ Θ₁ ⊊ Θ_P} (−1)^{|Θ_P \ Θ₁|} τ_R^{Θ₁} τ̂_{Θ₁}^P`
  (the remark after Arthur 1978, Corollary 6.2);
* `epsilon_mul_phi_eq_sum`: Arthur's identity `(6.2) = (6.4)`;
* `langlandsCombinatorial_eq`: the lemma, by strong induction on `Θ_P`;
* `langlandsCombinatorialLemmaStatement`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.ArthurCombinatorics

open Finset

variable {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N}

/-- `τ_P^P = 1`. -/
theorem tau_self (Θ : Finset ι) (H : N) : tau P Θ Θ H = 1 := by
  unfold tau
  rw [ite_eq_left]
  intro i hi
  rw [Finset.sdiff_self] at hi
  exact absurd hi (notMem_empty i)

/-- `τ̂_P^P = 1`. -/
theorem tauHat_self (Θ : Finset ι) (H : N) : tauHat P Θ Θ H = 1 := by
  unfold tauHat
  rw [ite_eq_left]
  intro i hi
  rw [Finset.sdiff_self] at hi
  exact absurd hi (notMem_empty i)

/-- **Arthur 1978, (6.2) = (6.4).** For `Θ_Q ⊆ Θ_P`,
`ε_Q^P(Λ) φ_Q^P(Λ, H) = ∑_{Θ_Q ⊆ Θ₁ ⊆ Θ_P} (−1)^{|Θ_P \ Θ₁|} τ̂_{Θ₁}^P(H) [Θ₁ ⊆ Θ_Λ]`, where
`Θ₁ ⊆ Θ_Λ` means `Λ(α^∨) > 0` for every `α ∈ Δ_Q^{P_1}`. -/
theorem epsilon_mul_phi_eq_sum {ΘQ ΘP : Finset ι} (hQP : ΘQ ⊆ ΘP) (Λ : M) (H : N) :
    epsilon P ΘQ ΘP Λ * phi P ΘQ ΘP Λ H =
      ∑ Θ₁ ∈ ΘP.powerset.filter (ΘQ ⊆ ·), (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H *
        (if ∃ i ∈ Θ₁ \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then 0 else 1) := by
  classical
  set L := ΘP.filter fun i => i ∈ ΘQ ∨ 0 < corootValue P ΘQ Λ i with hLdef
  set A := ΘQ ∪ ΘP.filter fun i => weightCoordinate P ΘP i H ≤ 0 with hAdef
  have hLP : L ⊆ ΘP := filter_subset _ _
  have hQL : ΘQ ⊆ L := fun i hi => mem_filter.mpr ⟨hQP hi, Or.inl hi⟩
  have hQA : ΘQ ⊆ A := subset_union_left
  -- the terms of the right-hand side
  have hterm : ∀ Θ₁ ∈ ΘP.powerset.filter (ΘQ ⊆ ·),
      (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H *
          (if ∃ i ∈ Θ₁ \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then 0 else 1) =
        if A ⊆ Θ₁ ∧ Θ₁ ⊆ L then (-1 : ℤ) ^ (ΘP \ Θ₁).card else 0 := by
    intro Θ₁ hΘ₁
    rw [mem_filter, mem_powerset] at hΘ₁
    obtain ⟨h1P, hQ1⟩ := hΘ₁
    have hhat : tauHat P Θ₁ ΘP H = if A ⊆ Θ₁ then 1 else 0 := by
      unfold tauHat
      congr 1
      refine propext ⟨fun h => union_subset hQ1 fun i hi => ?_, fun h i hi => ?_⟩
      · obtain ⟨hiP, hle⟩ := mem_filter.mp hi
        by_contra hi1
        exact absurd (h i (mem_sdiff.mpr ⟨hiP, hi1⟩)) (not_lt.mpr hle)
      · obtain ⟨hiP, hi1⟩ := mem_sdiff.mp hi
        by_contra hle
        exact hi1 (h (mem_union_right _ (mem_filter.mpr ⟨hiP, not_lt.mp hle⟩)))
    have hL : (∃ i ∈ Θ₁ \ ΘQ, corootValue P ΘQ Λ i ≤ 0) ↔ ¬ Θ₁ ⊆ L := by
      constructor
      · rintro ⟨i, hi, hle⟩ hsub
        obtain ⟨hi1, hiQ⟩ := mem_sdiff.mp hi
        rcases (mem_filter.mp (hsub hi1)).2 with hq | hpos
        · exact hiQ hq
        · exact absurd hpos (not_lt.mpr hle)
      · intro hns
        obtain ⟨i, hi1, hiL⟩ := not_subset.mp hns
        refine ⟨i, mem_sdiff.mpr ⟨hi1, fun hq => hiL (hQL hq)⟩, ?_⟩
        by_contra hpos
        exact hiL (mem_filter.mpr ⟨h1P hi1, Or.inr (not_le.mp hpos)⟩)
    have hite : (if ∃ i ∈ Θ₁ \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then (0 : ℤ) else 1) =
        if Θ₁ ⊆ L then 1 else 0 := by
      by_cases hb : Θ₁ ⊆ L
      · rw [ite_eq_right fun h => hL.mp h hb, ite_eq_left hb]
      · rw [ite_eq_left (hL.mpr hb), ite_eq_right hb]
    rw [hhat, hite]
    by_cases ha : A ⊆ Θ₁ <;> by_cases hb : Θ₁ ⊆ L <;> simp [ha, hb]
  rw [sum_congr rfl hterm, ← sum_filter, filter_filter]
  have hset : (ΘP.powerset.filter fun Θ₁ => ΘQ ⊆ Θ₁ ∧ (A ⊆ Θ₁ ∧ Θ₁ ⊆ L)) =
      L.powerset.filter (A ⊆ ·) := by
    ext Θ₁
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨-, -, hA1, h1L⟩
      exact ⟨h1L, hA1⟩
    · rintro ⟨h1L, hA1⟩
      exact ⟨h1L.trans hLP, hQA.trans hA1, hA1, h1L⟩
  rw [hset]
  -- the left-hand side
  have heps : epsilon P ΘQ ΘP Λ = (-1) ^ (ΘP \ L).card := by
    unfold epsilon
    congr 2
    ext i
    rw [mem_filter, mem_sdiff, mem_sdiff]
    constructor
    · rintro ⟨⟨hiP, hiQ⟩, hle⟩
      refine ⟨hiP, fun h => ?_⟩
      rcases (mem_filter.mp h).2 with hq | hpos
      · exact hiQ hq
      · exact absurd hpos (not_lt.mpr hle)
    · rintro ⟨hiP, hiL⟩
      refine ⟨⟨hiP, fun hq => hiL (hQL hq)⟩, ?_⟩
      by_contra hpos
      exact hiL (mem_filter.mpr ⟨hiP, Or.inr (not_le.mp hpos)⟩)
  have hphi : phi P ΘQ ΘP Λ H = if A = L then 1 else 0 := by
    unfold phi
    congr 1
    refine propext ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      constructor
      · intro hiA
        rcases mem_union.mp hiA with hq | hf
        · exact hQL hq
        · obtain ⟨hiP, hle⟩ := mem_filter.mp hf
          refine mem_filter.mpr ⟨hiP, ?_⟩
          by_cases hq : i ∈ ΘQ
          · exact Or.inl hq
          · refine Or.inr ?_
            by_contra hc
            exact absurd hle (not_le.mpr ((h i (mem_sdiff.mpr ⟨hiP, hq⟩)).1 (not_lt.mp hc)))
      · intro hiL
        obtain ⟨hiP, hor⟩ := mem_filter.mp hiL
        by_cases hq : i ∈ ΘQ
        · exact mem_union_left _ hq
        · have hpos := hor.resolve_left hq
          exact mem_union_right _
            (mem_filter.mpr ⟨hiP, (h i (mem_sdiff.mpr ⟨hiP, hq⟩)).2 hpos⟩)
    · obtain ⟨hiP, hq⟩ := mem_sdiff.mp hi
      refine ⟨fun hc => ?_, fun hpos => ?_⟩
      · by_contra hle
        have hiA : i ∈ A := mem_union_right _ (mem_filter.mpr ⟨hiP, not_lt.mp hle⟩)
        rw [h] at hiA
        rcases (mem_filter.mp hiA).2 with hq' | hpos
        · exact hq hq'
        · exact absurd hc (not_le.mpr hpos)
      · have hiL : i ∈ L := mem_filter.mpr ⟨hiP, Or.inr hpos⟩
        rw [← h] at hiL
        rcases mem_union.mp hiL with hq' | hf
        · exact absurd hq' hq
        · exact (mem_filter.mp hf).2
  rw [heps, hphi]
  by_cases hAL : A ⊆ L
  · have hrw : ∀ Θ₁ ∈ L.powerset.filter (A ⊆ ·),
        (-1 : ℤ) ^ (ΘP \ Θ₁).card = (-1) ^ (ΘP \ L).card * (-1) ^ (L \ Θ₁).card := by
      intro Θ₁ hΘ₁
      rw [mem_filter, mem_powerset] at hΘ₁
      rw [card_sdiff_trans hΘ₁.1 hLP, pow_add]
    rw [sum_congr rfl hrw, ← mul_sum, alternatingSum_eq A L hAL]
  · have hempty : ∀ Θ₁ ∈ L.powerset.filter (A ⊆ ·), (-1 : ℤ) ^ (ΘP \ Θ₁).card = 0 := by
      intro Θ₁ hΘ₁
      rw [mem_filter, mem_powerset] at hΘ₁
      exact absurd (hΘ₁.2.trans hΘ₁.1) hAL
    rw [sum_congr rfl hempty, sum_const_zero, ite_eq_right fun h => hAL h.subset, mul_zero]

variable [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] {b : P.Base}

/-- **The remark after Arthur 1978, Corollary 6.2**, solved for `τ_R^P`: for `Θ_R ⊊ Θ_P`,
`τ_R^P(H) = −∑_{Θ_R ⊆ Θ₁ ⊊ Θ_P} (−1)^{|Θ_P \ Θ₁|} τ_R^{Θ₁}(H) τ̂_{Θ₁}^P(H)`. -/
theorem tau_eq_neg_sum {ΘR ΘP : Finset ι} (hRP : ΘR ⊆ ΘP) (hP : ΘP ⊆ b.support)
    (hne : ΘR ≠ ΘP) (H : N) :
    tau P ΘR ΘP H = -∑ Θ₁ ∈ (ΘP.powerset.filter (ΘR ⊆ ·)).erase ΘP,
      (-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H := by
  have hmem : ΘP ∈ ΘP.powerset.filter (ΘR ⊆ ·) :=
    mem_filter.mpr ⟨mem_powerset_self _, hRP⟩
  have h0 := tauTauHat_sum_eq_sigma (P := P) ΘR ΘP H
  rw [sigma_self_eq_zero (b := b) hRP hP hne H, mul_zero, ← add_sum_erase _ _ hmem,
    Finset.sdiff_self, card_empty, pow_zero, one_mul, tauHat_self, mul_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- **Arthur 1978, Lemma 6.3** (Langlands' combinatorial lemma), by strong induction on `Θ_P`. -/
theorem langlandsCombinatorial_eq (ΘQ : Finset ι) (Λ : M) (H : N) :
    ∀ ΘP : Finset ι, ΘQ ⊆ ΘP → ΘP ⊆ b.support →
      ∑ ΘR ∈ ΘP.powerset.filter (ΘQ ⊆ ·),
          epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR ΘP H =
        if ∃ i ∈ ΘP \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then 0 else 1 := by
  intro ΘP
  induction ΘP using Finset.strongInduction with
  | H ΘP ih =>
  intro hQP hP
  set g : Finset ι → ℤ := fun Θ₁ => if ∃ i ∈ Θ₁ \ ΘQ, corootValue P ΘQ Λ i ≤ 0 then 0 else 1
    with hgdef
  set I := ΘP.powerset.filter (ΘQ ⊆ ·) with hIdef
  have hPI : ΘP ∈ I := mem_filter.mpr ⟨mem_powerset_self _, hQP⟩
  -- (6.2) = (6.4), with the term `Θ₁ = Θ_P` split off
  have hE := epsilon_mul_phi_eq_sum (P := P) hQP Λ H
  rw [← add_sum_erase _ _ hPI, Finset.sdiff_self, card_empty, pow_zero, one_mul, tauHat_self,
    one_mul] at hE
  -- the terms `Θ_R ≠ Θ_P` give `−(6.3)`
  have hrest : ∑ ΘR ∈ I.erase ΘP, epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR ΘP H =
      -∑ Θ₁ ∈ I.erase ΘP, (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H * g Θ₁ := by
    have hτ : ∀ ΘR ∈ I.erase ΘP,
        epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR ΘP H =
          -∑ Θ₁ ∈ (ΘP.powerset.filter (ΘR ⊆ ·)).erase ΘP,
            epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H *
              ((-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H) := by
      intro ΘR hR
      obtain ⟨hRne, hRI⟩ := mem_erase.mp hR
      rw [mem_filter, mem_powerset] at hRI
      rw [tau_eq_neg_sum (b := b) hRI.1 hP hRne H, mul_neg, mul_sum]
    have hswap : ∑ ΘR ∈ I.erase ΘP, ∑ Θ₁ ∈ (ΘP.powerset.filter (ΘR ⊆ ·)).erase ΘP,
          epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H *
            ((-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H) =
        ∑ Θ₁ ∈ I.erase ΘP, ∑ ΘR ∈ Θ₁.powerset.filter (ΘQ ⊆ ·),
          epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H *
            ((-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H) := by
      refine sum_comm' fun ΘR Θ₁ => ?_
      simp only [hIdef, mem_erase, mem_filter, mem_powerset]
      constructor
      · rintro ⟨⟨-, hRP, hQR⟩, h1ne, h1P, hR1⟩
        exact ⟨⟨hR1, hQR⟩, h1ne, h1P, hQR.trans hR1⟩
      · rintro ⟨⟨hR1, hQR⟩, h1ne, h1P, -⟩
        refine ⟨⟨fun hRe => h1ne (Subset.antisymm h1P (hRe ▸ hR1)), hR1.trans h1P, hQR⟩,
          h1ne, h1P, hR1⟩
    have hinner : ∀ Θ₁ ∈ I.erase ΘP, ∑ ΘR ∈ Θ₁.powerset.filter (ΘQ ⊆ ·),
          epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H *
            ((-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H) =
        (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H * g Θ₁ := by
      intro Θ₁ h1
      obtain ⟨h1ne, h1I⟩ := mem_erase.mp h1
      rw [mem_filter, mem_powerset] at h1I
      have hss : Θ₁ ⊂ ΘP := Finset.ssubset_iff_subset_ne.mpr ⟨h1I.1, h1ne⟩
      have hih := ih Θ₁ hss h1I.2 (h1I.1.trans hP)
      calc ∑ ΘR ∈ Θ₁.powerset.filter (ΘQ ⊆ ·), epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H *
              ((-1 : ℤ) ^ (ΘP \ Θ₁).card * tau P ΘR Θ₁ H * tauHat P Θ₁ ΘP H)
          = (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H *
              ∑ ΘR ∈ Θ₁.powerset.filter (ΘQ ⊆ ·),
                epsilon P ΘQ ΘR Λ * phi P ΘQ ΘR Λ H * tau P ΘR Θ₁ H := by
            rw [mul_sum]
            exact sum_congr rfl fun _ _ => by ring
        _ = (-1 : ℤ) ^ (ΘP \ Θ₁).card * tauHat P Θ₁ ΘP H * g Θ₁ := by rw [hih]
    rw [sum_congr rfl hτ, sum_neg_distrib, hswap, sum_congr rfl hinner]
  rw [← add_sum_erase _ _ hPI, tau_self, mul_one, hrest, hE]
  ring

/-- **Arthur 1978, Lemma 6.3.** -/
theorem langlandsCombinatorialLemmaStatement : LanglandsCombinatorialLemmaStatement.{u} := by
  intro ι M N _ _ _ _ _ _ P _ _ b ΘQ ΘP hQP hP Λ H
  exact langlandsCombinatorial_eq (b := b) ΘQ Λ H ΘP hQP hP

end Langlands.ArthurCombinatorics
