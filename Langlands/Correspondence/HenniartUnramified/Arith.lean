import Langlands.Correspondence.HenniartPolarPartClosedFormulaProof
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! # Counting lemmas for unramified descent -/

noncomputable section

namespace Langlands.Henniart.Numerical

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- A relation that is a bijection between two sets identifies their cardinalities. -/
theorem encard_eq_of_rel {α β : Type*} {S : Set α} {T : Set β} (R : α → β → Prop)
    (h1 : ∀ a ∈ S, ∃ b ∈ T, R a b) (h2 : ∀ b ∈ T, ∃ a ∈ S, R a b)
    (hf : ∀ a ∈ S, ∀ b ∈ T, ∀ b' ∈ T, R a b → R a b' → b = b')
    (hi : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') :
    S.encard = T.encard := by
  classical
  let g : S → T := fun a => ⟨Classical.choose (h1 a a.2), (Classical.choose_spec (h1 a a.2)).1⟩
  have hg : ∀ a : S, R a (g a) := fun a => (Classical.choose_spec (h1 a a.2)).2
  have hinj : Function.Injective g := by
    intro a a' h
    apply Subtype.ext
    apply hi a a.2 a' a'.2 (g a) (g a).2 (hg a)
    rw [h]
    exact hg a'
  have hsurj : Function.Surjective g := by
    intro b
    obtain ⟨a, ha, hab⟩ := h2 b b.2
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    exact (hf a ha b b.2 (g ⟨a, ha⟩) (g ⟨a, ha⟩).2 hab (hg ⟨a, ha⟩)).symm
  exact Set.encard_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

/-- A functional relation whose fibers all have exactly `f` elements multiplies cardinalities
by `f`. -/
theorem encard_eq_mul_of_fibers {α β : Type*} {S : Set α} {T : Set β} (R : α → β → Prop)
    (f : ℕ) (h1 : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (hf : ∀ a ∈ S, ∀ b ∈ T, ∀ b' ∈ T, R a b → R a b' → b = b')
    (h3 : ∀ b ∈ T, ∃ g : Fin f → α, Function.Injective g ∧ (∀ j, g j ∈ S ∧ R (g j) b) ∧
      ∀ a ∈ S, R a b → ∃ j, g j = a) :
    S.encard = T.encard * f := by
  classical
  choose G hGinj hGmem hGall using h3
  let Φ : T × Fin f → S := fun x => ⟨G x.1 x.1.2 x.2, (hGmem x.1 x.1.2 x.2).1⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨b, hb⟩, j⟩ ⟨⟨b', hb'⟩, j'⟩ h
    have h' : G b hb j = G b' hb' j' := congrArg Subtype.val h
    have hab : R (G b' hb' j') b := h' ▸ (hGmem b hb j).2
    have hbb : b = b' := hf _ (hGmem b' hb' j').1 b hb b' hb' hab (hGmem b' hb' j').2
    subst hbb
    have hj : j = j' := hGinj b hb h'
    rw [hj]
  have hsurj : Function.Surjective Φ := by
    intro a
    obtain ⟨b, hb, hab⟩ := h1 a a.2
    obtain ⟨j, hj⟩ := hGall b hb a a.2 hab
    exact ⟨(⟨b, hb⟩, j), Subtype.ext hj⟩
  have e : (T × Fin f) ≃ S := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  change ENat.card S = ENat.card T * f
  rw [← ENat.card_congr e, ENat.card_prod, ENat.card_eq_coe_fintype_card (α := Fin f),
    Fintype.card_fin]

/-- Möbius inversion of the counts of points with a given minimal period. -/
theorem moebius_count {α : Type*} (Z : Finset α) (mp : α → ℕ) {f : ℕ} (hf : 0 < f) :
    ((Z.filter fun x => mp x = f).card : ℤ) =
      ∑ i ∈ f.divisors, (μ (f / i) : ℤ) * ((Z.filter fun x => mp x ∣ i).card : ℤ) := by
  classical
  have key : ∀ n > 0, ∑ d ∈ n.divisors, ((Z.filter fun x => mp x = d).card : ℤ) =
      ((Z.filter fun x => mp x ∣ n).card : ℤ) := by
    intro n hn
    rw [Finset.card_eq_sum_card_fiberwise (f := mp) (t := n.divisors)]
    · push_cast
      refine Finset.sum_congr rfl fun d hd => ?_
      congr 2
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, rfl⟩
        exact ⟨⟨hx, (Nat.mem_divisors.mp hd).1⟩, rfl⟩
      · rintro ⟨⟨hx, -⟩, h⟩
        exact ⟨hx, h⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      exact Nat.mem_divisors.mpr ⟨hx.2, hn.ne'⟩
  have h := (sum_eq_iff_sum_mul_moebius_eq.mp key) f hf
  rw [← h]
  simp only [Int.cast_id]
  exact Nat.sum_divisorsAntidiagonal' (fun x y => μ x * ((Z.filter fun z => mp z ∣ y).card : ℤ))

/-- The polar-part counts satisfy Möbius inversion against the torsion-one counts over the
unramified extensions of degree dividing `f`. -/
theorem polar_moebius (q : ℕ) (hq : IsPrimePow q) (n f s : ℕ) (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hfn : f ∣ n) (hfs : f ∣ s) :
    (f : ℤ) * (polarPartCount q n f s : ℤ) =
      ∑ i ∈ f.divisors, (μ (f / i) : ℤ) * (polarTwistCount (q ^ i) (n / f) (s / f) : ℤ) := by
  have hnf : 1 ≤ n / f := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hfn)
  have hqi : ∀ i ∈ f.divisors, IsPrimePow (q ^ i) := fun i hi =>
    hq.pow (Nat.pos_of_mem_divisors hi).ne'
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have h0 := (polarPartClosedFormula q hq n f 0 hn hf hfn hfs).2 rfl
    by_cases hfn' : f = n
    · subst hfn'
      rw [h0.2]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.div_self (by omega), Nat.zero_div]
      have h1 := ((polarPartClosedFormula (q ^ i) (hqi i hi) 1 1 0 le_rfl le_rfl
        (dvd_refl 1) (dvd_zero 1)).2 rfl).2
      unfold polarTwistCount
      simp only [Nat.cast_one, one_mul, Nat.divisors_one, Finset.sum_singleton,
        Nat.div_self one_pos, moebius_apply_one, pow_one] at h1
      rw [h1]
      push_cast
      ring
    · rw [h0.1 hfn', Nat.cast_zero, mul_zero]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : (1 : ℕ) ≠ n / f := by
        intro h
        apply hfn'
        have := Nat.div_mul_cancel hfn
        rw [← h, one_mul] at this
        exact this
      have h1 := ((polarPartClosedFormula (q ^ i) (hqi i hi) (n / f) 1 0 hnf le_rfl
        (one_dvd _) (dvd_zero 1)).2 rfl).1 hne
      unfold polarTwistCount
      rw [Nat.zero_div, h1, Nat.cast_zero, mul_zero]
  · rw [(polarPartClosedFormula q hq n f s hn hf hfn hfs).1 hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsf : 1 ≤ s / f := (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd hs hfs)
    have h1 := (polarPartClosedFormula (q ^ i) (hqi i hi) (n / f) 1 (s / f) hnf le_rfl
      (one_dvd _) (one_dvd _)).1 hsf
    unfold polarTwistCount
    simp only [Nat.cast_one, one_mul, Nat.divisors_one, Finset.sum_singleton,
      Nat.div_self one_pos, moebius_apply_one, pow_one, Nat.div_one] at h1
    rw [h1]
    push_cast
    rw [mul_assoc]
    congr 2
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [pow_mul]

/-- The same identity for every `q`: when `q` is not a prime power both sides vanish. -/
theorem polar_moebius_of_le (q : ℕ) (n f s : ℕ) (hn : 1 ≤ n) (hf : 1 ≤ f) (hfn : f ∣ n)
    (hfs : f ∣ s) :
    (f : ℤ) * (polarPartCount q n f s : ℤ) =
      ∑ i ∈ f.divisors, (μ (f / i) : ℤ) * (polarTwistCount (q ^ i) (n / f) (s / f) : ℤ) := by
  by_cases hq : IsPrimePow q
  · exact polar_moebius q hq n f s hn hf hfn hfs
  · have h0 : ∀ q' n' f' s' : ℕ, ¬ IsPrimePow q' → polarPartCount q' n' f' s' = 0 := by
      intro q' n' f' s' hq'
      unfold polarPartCount
      split_ifs with h
      · exact absurd h.1 hq'
      · rfl
    rw [h0 q n f s hq, Nat.cast_zero, mul_zero]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    unfold polarTwistCount
    rw [h0 _ _ _ _ (fun h => hq ((isPrimePow_pow_iff (Nat.pos_of_mem_divisors hi).ne').mp h)),
      Nat.cast_zero, mul_zero]

end Langlands.Henniart.Numerical
