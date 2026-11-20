import Langlands.Global.Factors.CuspidalPairPoleStatement
import Mathlib.Analysis.Meromorphic.NormalForm

/-! # Continuation from normalized Rankin–Selberg tests -/

noncomputable section

set_option autoImplicit false

open Filter Set Topology

namespace Langlands.Global.CuspidalPairPoles

private def poleDenominator (s : ℂ) : ℂ := s * (s - 1)

private theorem poleDenominator_ne_zero {s : ℂ} (hs : s ∉ ({0, 1} : Set ℂ)) :
    poleDenominator s ≠ 0 := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hs
  exact mul_ne_zero hs.1 (sub_ne_zero.mpr hs.2)

private theorem not_pole_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    s ∉ ({0, 1} : Set ℂ) := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨fun h => by norm_num [h] at hs, fun h => by norm_num [h] at hs⟩

private theorem analyticAt_poleDenominator (s : ℂ) : AnalyticAt ℂ poleDenominator s := by
  unfold poleDenominator
  fun_prop

private theorem poleDenominator_order {s : ℂ} (hs : s ∈ ({0, 1} : Set ℂ)) :
    meromorphicOrderAt poleDenominator s = 1 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · have h : AnalyticAt ℂ (fun z : ℂ => z - 1) 0 := by fun_prop
    change meromorphicOrderAt ((id : ℂ → ℂ) * (· - 1)) 0 = 1
    rw [meromorphicOrderAt_mul (MeromorphicAt.id 0) h.meromorphicAt,
      h.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by norm_num), add_zero]
    exact meromorphicOrderAt_id
  · have h : AnalyticAt ℂ (fun z : ℂ => z) 1 := analyticAt_id
    change meromorphicOrderAt ((fun z : ℂ => z) * (· - 1)) 1 = 1
    rw [meromorphicOrderAt_mul h.meromorphicAt (by fun_prop),
      h.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by norm_num), zero_add]
    exact meromorphicOrderAt_id_sub_const

/-- Multiply by `s * (s - 1)` and take the meromorphic normal form to fill the two
removable singularities when `I` is holomorphic elsewhere with at most simple poles. -/
def regularizeSimplePoles (I : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => poleDenominator s * I s) univ

/-- Regularization is entire, agrees with the cleared function away from the two
points, and is nonzero at an exceptional point exactly when `I` has a pole there. -/
theorem regularizeSimplePoles_spec {I : ℂ → ℂ}
    (hI : DifferentiableOn ℂ I ({0, 1} : Set ℂ)ᶜ)
    (hp : ∀ p ∈ ({0, 1} : Set ℂ), MeromorphicAt I p ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt I p) :
    AnalyticOnNhd ℂ (regularizeSimplePoles I) univ ∧
      (∀ s ∉ ({0, 1} : Set ℂ), regularizeSimplePoles I s = s * (s - 1) * I s) ∧
      ∀ p ∈ ({0, 1} : Set ℂ), regularizeSimplePoles I p ≠ 0 ↔ meromorphicOrderAt I p < 0 := by
  let f : ℂ → ℂ := fun s => poleDenominator s * I s
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  have hAnalytic s (hs : s ∉ ({0, 1} : Set ℂ)) : AnalyticAt ℂ f s :=
    (analyticAt_poleDenominator s).mul (hI.analyticAt (hopen.mem_nhds hs))
  have hF : MeromorphicOn f univ := by
    intro s _
    by_cases hs : s ∈ ({0, 1} : Set ℂ)
    · exact (analyticAt_poleDenominator s).meromorphicAt.mul (hp s hs).1
    · exact (hAnalytic s hs).meromorphicAt
  have hOrder p (hs : p ∈ ({0, 1} : Set ℂ)) :
      meromorphicOrderAt (regularizeSimplePoles I) p = 1 + meromorphicOrderAt I p := by
    change meromorphicOrderAt (toMeromorphicNFOn f univ) p = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hF (mem_univ p)]
    change meromorphicOrderAt (poleDenominator * I) p = _
    rw [meromorphicOrderAt_mul (analyticAt_poleDenominator p).meromorphicAt (hp p hs).1,
      poleDenominator_order hs]
  have hNF : MeromorphicNFOn (regularizeSimplePoles I) univ :=
    meromorphicNFOn_toMeromorphicNFOn f univ
  have hOff s (hs : s ∉ ({0, 1} : Set ℂ)) : regularizeSimplePoles I s = f s := by
    change toMeromorphicNFOn f univ s = f s
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hF (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (hAnalytic s hs).meromorphicNFAt]
  refine ⟨fun s hs => (hNF hs).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_, hOff, ?_⟩
  · by_cases hpole : s ∈ ({0, 1} : Set ℂ)
    · rw [hOrder s hpole]
      have h := add_le_add_right (hp s hpole).2 (1 : WithTop ℤ)
      have hone : (1 : WithTop ℤ) + (-1) = 0 := by norm_num
      rwa [hone] at h
    · change 0 ≤ meromorphicOrderAt (toMeromorphicNFOn f univ) s
      rw [meromorphicOrderAt_toMeromorphicNFOn hF hs]
      exact (hAnalytic s hpole).meromorphicOrderAt_nonneg
  · intro p hpole
    rw [← (hNF (mem_univ p)).meromorphicOrderAt_eq_zero_iff, hOrder p hpole]
    have hb := (hp p hpole).2
    cases h : meromorphicOrderAt I p with
    | top => simp
    | coe n =>
      rw [h] at hb
      have hn : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp hb
      norm_cast
      omega

private theorem exists_entire_quotient {ι : Type*} (J R : ι → ℂ → ℂ) (A : ℂ → ℂ)
    (hJ : ∀ i, AnalyticOnNhd ℂ (J i) univ) (hR : ∀ i, AnalyticOnNhd ℂ (R i) univ)
    (hCover : ∀ s, ∃ i, R i s ≠ 0)
    (hA : ∃ σ : ℝ, ContinuousOn A {s | σ < s.re})
    (hMatch : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → J i s = R i s * A s) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ (∀ i s, J i s = R i s * H s) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → H s = A s := by
  have hcross i j : ∀ s, R i s * J j s = R j s * J i s := by
    obtain ⟨a, ha⟩ := hMatch i
    obtain ⟨b, hb⟩ := hMatch j
    let z : ℂ := (max a b + 1 : ℝ)
    have haz : a < z.re := by change a < max a b + 1; linarith [le_max_left a b]
    have hbz : b < z.re := by change b < max a b + 1; linarith [le_max_right a b]
    have hea : ∀ᶠ s : ℂ in 𝓝 z, a < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds haz
    have heb : ∀ᶠ s : ℂ in 𝓝 z, b < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hbz
    have hlocal : (fun s => R i s * J j s) =ᶠ[𝓝 z] (fun s => R j s * J i s) := by
      filter_upwards [hea, heb] with s hs hs'
      rw [ha s hs, hb s hs', mul_left_comm]
    exact congrFun ((hR i |>.mul (hJ j)).eq_of_eventuallyEq (hR j |>.mul (hJ i)) hlocal)
  let H (s : ℂ) : ℂ := J (hCover s).choose s / R (hCover s).choose s
  have hH i s : J i s = R i s * H s := by
    change J i s = R i s * (J (hCover s).choose s / R (hCover s).choose s)
    rw [← mul_div_assoc, hcross i (hCover s).choose s,
      mul_div_cancel_left₀ _ (hCover s).choose_spec]
  have hHa : AnalyticOnNhd ℂ H univ := by
    intro s hs
    obtain ⟨i, hi⟩ := hCover s
    have he : ∀ᶠ z in 𝓝 s, R i z ≠ 0 := (hR i s hs).continuousAt.eventually_ne hi
    refine ((hJ i s hs).div (hR i s hs) hi).congr ?_
    filter_upwards [he] with z hz
    exact (div_eq_iff hz).2 (by rw [hH i z, mul_comm])
  refine ⟨H, hHa, hH, ?_⟩
  obtain ⟨i, hi⟩ := hCover 0
  obtain ⟨a, ha⟩ := hMatch i
  obtain ⟨b, hb⟩ := hA
  refine ⟨max a b, fun s hs => ?_⟩
  have hNear : ∀ᶠ z : ℂ in 𝓝 s, a < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (lt_of_le_of_lt (le_max_left a b) hs)
  have hne : ∀ᶠ z in 𝓝[≠] s, R i z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hR i s (mem_univ s)).meromorphicAt).mp
    intro he
    have hcont := (hR i s (mem_univ s)).continuousAt
    have hz : R i =ᶠ[𝓝 s] 0 :=
      (hcont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).1
        (meromorphicOrderAt_eq_top_iff.mp he)
    have hg : AnalyticOnNhd ℂ (0 : ℂ → ℂ) univ := fun _ _ => analyticAt_const
    exact hi (congrFun ((hR i).eq_of_eventuallyEq hg hz) 0)
  have he : H =ᶠ[𝓝[≠] s] A := by
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hne] with z hz hn
    exact mul_left_cancel₀ hn ((hH i z).symm.trans (ha z hz))
  have hAc : ContinuousAt A s := (hb s (lt_of_le_of_lt (le_max_right a b) hs)).continuousAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (lt_of_le_of_lt (le_max_right a b) hs))
  exact ((hHa s (mem_univ s)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hAc).1 he
    |>.eq_of_nhds

/-- Whole-plane continuation and the exact two-point pole criterion follow from
normalized test functions that are entire and have no common zero. Each test can
agree with the completed product on its own initial right half-plane. -/
theorem exists_continuation_of_normalized_tests {ι : Type*}
    (I R : ι → ℂ → ℂ) (L : ℂ → ℂ) (cond : Prop)
    (hI : ∀ i, DifferentiableOn ℂ (I i) ({0, 1} : Set ℂ)ᶜ)
    (hOrder : ∀ i p, p ∈ ({0, 1} : Set ℂ) → MeromorphicAt (I i) p ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (I i) p)
    (hR : ∀ i, AnalyticOnNhd ℂ (R i) univ) (hCover : ∀ s, ∃ i, R i s ≠ 0)
    (hL : ∃ σ : ℝ, ContinuousOn L {s | σ < s.re})
    (hMatch : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I i s = R i s * L s)
    (hPole : ∀ p ∈ ({0, 1} : Set ℂ), (∃ i, meromorphicOrderAt (I i) p < 0) ↔ cond) :
    ∃ Λ : ℂ → ℂ, (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Λ s = L s) ∧
      (∀ i s, s ∉ ({0, 1} : Set ℂ) → I i s = R i s * Λ s) ∧ HasSimplePoleProfile Λ cond := by
  let J i := regularizeSimplePoles (I i)
  let A s := poleDenominator s * L s
  have hJ i := regularizeSimplePoles_spec (hI i) (hOrder i)
  have hA : ∃ σ : ℝ, ContinuousOn A {s | σ < s.re} := by
    obtain ⟨σ, hσ⟩ := hL
    exact ⟨σ, fun s hs => (analyticAt_poleDenominator s).continuousAt.continuousWithinAt.mul (hσ s hs)⟩
  have hJMatch i : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → J i s = R i s * A s := by
    obtain ⟨σ, hσ⟩ := hMatch i
    refine ⟨max σ 1, fun s hs => ?_⟩
    have hs' := not_pole_of_one_lt_re (lt_of_le_of_lt (le_max_right σ 1) hs)
    change regularizeSimplePoles (I i) s = R i s * (s * (s - 1) * L s)
    rw [(hJ i).2.1 s hs', hσ s (lt_of_le_of_lt (le_max_left _ _) hs), mul_left_comm]
  obtain ⟨H, hH, hRelation, σ, hσ⟩ :=
    exists_entire_quotient J R A (fun i => (hJ i).1) hR hCover hA hJMatch
  let Λ s := H s / poleDenominator s
  have hAway i s (hs : s ∉ ({0, 1} : Set ℂ)) : I i s = R i s * Λ s := by
    have h := hRelation i s
    change regularizeSimplePoles (I i) s = _ at h
    rw [(hJ i).2.1 s hs] at h
    change I i s = R i s * (H s / poleDenominator s)
    rw [← mul_div_assoc, ← h]
    exact (mul_div_cancel_left₀ _ (poleDenominator_ne_zero hs)).symm
  refine ⟨Λ, ⟨max σ 1, fun s hs => ?_⟩, hAway, ?_, ?_⟩
  · have hs' := not_pole_of_one_lt_re (lt_of_le_of_lt (le_max_right σ 1) hs)
    change H s / poleDenominator s = L s
    rw [hσ s (lt_of_le_of_lt (le_max_left _ _) hs)]
    exact mul_div_cancel_left₀ _ (poleDenominator_ne_zero hs')
  · intro s hs
    exact ((hH s (mem_univ s)).div (analyticAt_poleDenominator s)
      (poleDenominator_ne_zero hs)).differentiableAt.differentiableWithinAt
  · intro p hp
    have hHp := hH p (mem_univ p)
    have hden := (analyticAt_poleDenominator p).meromorphicAt
    have heq : meromorphicOrderAt Λ p = meromorphicOrderAt H p - 1 := by
      change meromorphicOrderAt (H / poleDenominator) p = _
      rw [meromorphicOrderAt_div hHp.meromorphicAt hden, poleDenominator_order hp]
    refine ⟨hHp.meromorphicAt.div hden, ?_, ?_⟩
    · rw [heq, sub_eq_add_neg]
      simpa only [zero_add] using add_le_add_left hHp.meromorphicOrderAt_nonneg (-1 : WithTop ℤ)
    · have hHz : (∃ i, meromorphicOrderAt (I i) p < 0) ↔ H p ≠ 0 := by
        constructor
        · rintro ⟨i, hi⟩ hzero
          have hn := ((hJ i).2.2 p hp).2 hi
          exact hn (by simpa [J, hzero] using hRelation i p)
        · intro hnonzero
          obtain ⟨i, hi⟩ := hCover p
          exact ⟨i, ((hJ i).2.2 p hp).1 ((hRelation i p).trans_ne (mul_ne_zero hi hnonzero))⟩
      rw [← hPole p hp, hHz, ← hHp.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff, heq]
      have hn := hHp.meromorphicOrderAt_nonneg
      cases h : meromorphicOrderAt H p with
      | top => simp
      | coe n =>
        rw [h] at hn
        norm_cast at hn ⊢
        omega

/-- A finite linear combination of normalized factors equal to one gives the
strip bound from the corresponding linear combination of test integrals. -/
theorem isBoundedInVerticalStrips_of_normalized_sum {ι : Type*} (I R : ι → ℂ → ℂ)
    (Λ : ℂ → ℂ) (S : Finset ι) (c : ι → ℂ)
    (hRelation : ∀ i ∈ S, ∀ s ∉ ({0, 1} : Set ℂ), I i s = R i s * Λ s)
    (hSum : ∀ s ∉ ({0, 1} : Set ℂ), ∑ i ∈ S, c i * R i s = 1)
    (hBound : ∀ i ∈ S, IsBoundedInVerticalStrips (I i)) : IsBoundedInVerticalStrips Λ := by
  classical
  intro a b ε hε
  choose C hC using fun i : S => hBound i i.property a b ε hε
  refine ⟨∑ i : S, ‖c i‖ * C i, fun s ha hb hs₀ hs₁ => ?_⟩
  have hAway : s ∉ ({0, 1} : Set ℂ) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => by simp [h] at hs₀; linarith,
      fun h => by simp [h] at hs₁; linarith⟩
  have hI : ∑ i : S, c i * I i s = Λ s := by
    calc
      _ = ∑ i : S, (c i * R i s) * Λ s := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hRelation i i.property s hAway, mul_assoc]
      _ = (∑ i : S, c i * R i s) * Λ s := (Finset.sum_mul ..).symm
      _ = Λ s := by
        change (∑ i ∈ S.attach, c i * R i s) * Λ s = _
        rw [Finset.sum_attach S (fun i => c i * R i s), hSum s hAway, one_mul]
  rw [← hI]
  calc
    _ ≤ ∑ i : S, ‖c i * I i s‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC i s ha hb hs₀ hs₁) (norm_nonneg _)

end Langlands.Global.CuspidalPairPoles
