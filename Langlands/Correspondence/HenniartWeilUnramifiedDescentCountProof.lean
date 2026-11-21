import Langlands.Correspondence.HenniartUnramified.Strata

/-! # Unramified descent for the refined Weil strata -/

noncomputable section

namespace Langlands.Henniart

open Numerical Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

universe uK uW

/-- Unramified descent (Henniart 1988, Proposition 2.2; route note, Proposition `prop:unram`). -/
theorem weilUnramifiedDescentCount : WeilUnramifiedDescentCountStatement.{uK, uW} := by
  refine ⟨fun p _ K k s f hne => ?_, fun p _ K k s f hf hfn hfs hyp => ?_⟩
  · obtain ⟨c, hc⟩ := hne
    have hdvd := dvd_of_mem_weilRefinedStratum hc
    obtain ⟨σ, -, -, ht⟩ := hc
    obtain ⟨hpos, hdiv⟩ := weilTorsionNumber_pos_dvd_rank K σ
    rw [ht] at hpos hdiv
    exact ⟨hpos, hdiv, hdvd⟩
  · classical
    let φ := localGeometricFrobenius K
    have hφ : localDegree K φ = Multiplicative.ofAdd (1 : ℤ) := localGeometricFrobenius_degree K
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    obtain ⟨r, hrdef⟩ : ∃ r, (k + 1) / (m + 1) = r := ⟨_, rfl⟩
    obtain ⟨t, htdef⟩ : ∃ t, s / (m + 1) = t := ⟨_, rfl⟩
    have hr : (m + 1) * r = k + 1 := hrdef ▸ Nat.mul_div_cancel' hfn
    have ht : (m + 1) * t = s := htdef ▸ Nat.mul_div_cancel' hfs
    rw [hrdef, htdef] at hyp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, mul_zero] at hr
        omega
      · omega⟩
    let q := K.canonicalTopologicalData.residueCardinality
    let C := (weilSplit K φ hφ).conjType 1
    let G := goodTypes.{uK, uW} K φ hφ (r' + 1) t
    have hfixiff : ∀ (n : ℕ) (x : TypeClass.{uK, uW} (weilSplit K φ hφ)),
        (weilSplit K φ hφ).conjType n x = x ↔ Function.minimalPeriod C x ∣ n := by
      intro n x
      rw [← iterate_conjType]
      exact Function.isPeriodicPt_iff_minimalPeriod_dvd
    -- the fixed counts, from the hypothesis over the unramified extensions
    have hfix : ∀ j : ℕ, j + 1 ∣ m + 1 →
        {x ∈ G | (weilSplit K φ hφ).conjType (j + 1) x = x}.encard =
          (polarTwistCount (q ^ (j + 1)) (r' + 1) t : ℕ∞) := by
      intro j hj
      have h1 := hyp (j + 1) hj _ _ (unramifiedStage_isUnramifiedOfDegree K (j + 1))
      rw [unramifiedStage_residueCardinality, Nat.add_sub_cancel] at h1
      rw [← encard_fixed_goodTypes (φ := φ) (hφ := hφ) j r' t]
      exact h1
    -- finiteness
    have hfinZ : {x ∈ G | (weilSplit K φ hφ).conjType (m + 1) x = x}.Finite :=
      Set.finite_of_encard_eq_coe (hfix m (dvd_refl _))
    let Z := hfinZ.toFinset
    have hset : ∀ (P : ℕ → Prop) [DecidablePred P], (∀ d, P d → d ∣ m + 1) →
        {x ∈ G | P (Function.minimalPeriod C x)} =
          ((Z.filter fun x => P (Function.minimalPeriod C x) : Finset _) : Set _) := by
      intro P _ hP
      ext x
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Z]
      constructor
      · rintro ⟨hx, hPx⟩
        exact ⟨⟨hx, (hfixiff _ x).mpr (hP _ hPx)⟩, hPx⟩
      · rintro ⟨⟨hx, -⟩, hPx⟩
        exact ⟨hx, hPx⟩
    have hcardfix : ∀ i ∈ (m + 1).divisors,
        ((Z.filter fun x => Function.minimalPeriod C x ∣ i).card : ℤ) =
          (polarTwistCount (q ^ i) (r' + 1) t : ℤ) := by
      intro i hi
      have hi1 := Nat.pos_of_mem_divisors hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj := Nat.dvd_of_mem_divisors hi
      have h1 := hfix j hj
      have h2 : {x ∈ G | (weilSplit K φ hφ).conjType (j + 1) x = x} =
          {x ∈ G | Function.minimalPeriod C x ∣ j + 1} := by
        ext x
        simp only [Set.mem_ofPred_eq, hfixiff]
      rw [h2, hset (· ∣ j + 1) (fun d hd => hd.trans hj), Set.encard_coe_eq_coe_finsetCard]
        at h1
      exact_mod_cast h1
    -- the exact-period count
    have hP := encard_period_goodTypes (F := K) (φ := φ) (hφ := hφ) k s m (r' + 1) t hr ht
    rw [hset (· = m + 1) (fun d hd => hd ▸ dvd_refl _), Set.encard_coe_eq_coe_finsetCard] at hP
    have hmob := moebius_count Z (Function.minimalPeriod C) (Nat.succ_pos m)
    rw [Finset.sum_congr rfl fun i hi => by rw [hcardfix i hi]] at hmob
    have hpolar := polar_moebius_of_le q (k + 1) (m + 1) s (by omega) (by omega) hfn hfs
    rw [hrdef, htdef] at hpolar
    rw [← hpolar] at hmob
    -- conclude
    have htop : (weilRefinedStratum.{uK, uW} K k s (m + 1)).encard ≠ ⊤ := by
      intro h
      rw [h, ENat.top_mul (by exact_mod_cast (Nat.succ_ne_zero m))] at hP
      exact ENat.natCast_ne_top _ hP
    obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hw] at hP ⊢
    have hP' : (Z.filter fun x => Function.minimalPeriod C x = m + 1).card = w * (m + 1) := by
      exact_mod_cast hP
    rw [hP'] at hmob
    have hw' : w = polarPartCount q (k + 1) (m + 1) s := by
      have : ((w * (m + 1) : ℕ) : ℤ) = (((m + 1) * polarPartCount q (k + 1) (m + 1) s : ℕ) : ℤ) := by
        push_cast at hmob ⊢
        exact hmob
      have h2 : w * (m + 1) = (m + 1) * polarPartCount q (k + 1) (m + 1) s := by exact_mod_cast this
      rw [mul_comm] at h2
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h2
    rw [hw']

end Langlands.Henniart
