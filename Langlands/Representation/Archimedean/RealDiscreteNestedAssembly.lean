import Langlands.Representation.Archimedean.RealDiscreteSplitInjection
import Langlands.Representation.Archimedean.RealDiscreteNestedPresentation
import Langlands.Representation.Archimedean.RealTiedScalarAssembly

/-! # Principal series on both sides of a tied real standard module -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealDiscreteNestedAssembly

open Langlands.LocalFactor.Archimedean
open RealCharacterPairReducible RealDiscreteNestedPresentation RealStandardFiltration

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-- Adjacent splittings of a list of nonzero-weight blocks give an exact injection. -/
theorem split_injection {n : ℕ} :
    ∀ (ds : List ComplexCharacterData) (pre post : List RealBlock),
      realRank (pre ++ ds.map RealBlock.induced ++ post) = n → (∀ d ∈ ds, d.weight ≠ 0) →
      RealInjectiveIntertwinerExists n (pre ++ ds.map RealBlock.induced ++ post)
        (pre ++ (splitChars ds).map RealBlock.character ++ post)
  | [], pre, post, _, _ => by
    simpa [splitChars] using RealInjectiveIntertwinerExists.refl n (pre ++ post)
  | d :: ds, pre, post, hn, hw => by
    let tail := ds.map RealBlock.induced ++ post
    let pair := [RealBlock.character (high d), RealBlock.character (low d)]
    have hn' : realRank (pre ++ [RealBlock.induced d] ++ tail) = n := by simpa [tail] using hn
    have hl := Int.natAbs_pos.mpr (hw d List.mem_cons_self)
    have hinj : RealInjectiveIntertwinerExists n
        (pre ++ [RealBlock.induced d] ++ tail) (pre ++ pair ++ tail) :=
      ⟨_, RealDiscreteSplitInjection.splitInjection_injective_and_intertwines hn' hl
        (endpoint_signs d)⟩
    have hRank : realRank ((pre ++ pair) ++ ds.map RealBlock.induced ++ post) = n := by
      rw [List.append_assoc (pre ++ pair), ← hn']
      exact realRank_mid_eq pre tail rfl
    have hrec := split_injection ds (pre ++ pair) post hRank
      (fun e he => hw e (List.mem_cons_of_mem d he))
    have hrec' : RealInjectiveIntertwinerExists n (pre ++ pair ++ tail)
        (pre ++ (splitChars (d :: ds)).map RealBlock.character ++ post) := by
      simpa [tail, pair, splitChars, List.map_append, List.append_assoc] using hrec
    simpa [tail, List.append_assoc] using hinj.trans hrec'

/-- The donor list, with even center characters before the lows and odd center characters
after the highs. -/
def donorChars (even : List RealCharacterData) (ds : List ComplexCharacterData)
    (odd : List RealCharacterData) : List RealCharacterData :=
  even ++ nestedChars ds ++ odd

/-- The receiver has the same center characters and the high/low pairs adjacent. -/
def receiverChars (even : List RealCharacterData) (ds : List ComplexCharacterData)
    (odd : List RealCharacterData) : List RealCharacterData :=
  even ++ splitChars ds.reverse ++ odd

theorem donorChars_perm_receiverChars (even : List RealCharacterData)
    (ds : List ComplexCharacterData) (odd : List RealCharacterData) :
    (donorChars even ds odd).Perm (receiverChars even ds odd) :=
  ((nestedChars_perm_splitChars ds).append_left even).append_right odd

private theorem split_rank (ds : List ComplexCharacterData) :
    realRank ((splitChars ds).map RealBlock.character) = realRank (ds.map RealBlock.induced) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp [splitChars, realRank_cons, RealBlock.rank] at ih ⊢
    omega

private theorem exists_grouped (xs : List RealBlock) :
    ∃ (cs : List RealCharacterData) (ds : List ComplexCharacterData),
      xs.Perm (cs.map RealBlock.character ++ ds.map RealBlock.induced) := by
  induction xs with
  | nil => exact ⟨[], [], List.Perm.nil⟩
  | cons x xs ih =>
    obtain ⟨cs, ds, h⟩ := ih
    cases x with
    | character c => exact ⟨c :: cs, ds, h.cons _⟩
    | induced d =>
      exact ⟨cs, d :: ds, (h.cons _).trans List.perm_middle.symm⟩

private theorem surjection_of_two_injections {n : ℕ} {xs ys : List RealBlock}
    (hxy : RealInjectiveIntertwinerExists n xs ys)
    (hyx : RealInjectiveIntertwinerExists n ys xs) :
    RealSurjectiveIntertwinerExists n xs ys := by
  obtain ⟨T, hTi, hT⟩ := hxy
  obtain ⟨S, hSi, hS⟩ := hyx
  have hTs := RealSwapSurjective.surjective_of_injective
    (realStandardAdmissible n xs) (realStandardAdmissible n ys)
    (isRealGKModule_realStandardModule n ys).1 (isRealGKModule_realStandardModule n ys).2.1
    T (fun k f => hT.map_realStandardRep k f) hTi S (fun k f => hS.map_realStandardRep k f) hSi
  exact ⟨T, hTs, hT⟩

/-- Every tied list has a nested donor surjection and an adjacent receiver injection. -/
theorem exists_presentations {n : ℕ} {xs : List RealBlock} {r : ℝ}
    (hn : realRank xs = n) (ht : ∀ x ∈ xs, realBlockExponent x = r) :
    ∃ (even odd : List RealCharacterData) (ds : List ComplexCharacterData),
      (∀ c ∈ even, c.exponent.re = r ∧ c.parity = 0) ∧
      (∀ c ∈ odd, c.exponent.re = r ∧ c.parity = 1) ∧
      (∀ d ∈ ds, d.exponent.re = r ∧ 0 < d.weight.natAbs) ∧
      ds.Pairwise (fun d e => e.weight.natAbs ≤ d.weight.natAbs) ∧
      (donorChars even ds odd).length = n ∧
      RealSurjectiveIntertwinerExists n ((donorChars even ds odd).map RealBlock.character) xs ∧
      RealInjectiveIntertwinerExists n xs ((receiverChars even ds odd).map RealBlock.character) := by
  let ys := xs.flatMap realBlockExpand
  have hysRank : realRank ys = n := (realRank_flatMap_expand xs).trans hn
  have hysMod : realStandardModule n xs = realStandardModule n ys := by
    simpa only [ys, List.nil_append] using realStandardModule_append_flatMap_expand n xs []
  have hys (y : RealBlock) (hy : y ∈ ys) : realBlockExponent y = r ∧ IsRealBlockNondegenerate y := by
    obtain ⟨x, hx, hxy⟩ := List.mem_flatMap.mp hy
    exact ⟨(realBlockExponent_of_mem_expand hxy).trans (ht x hx),
      isRealBlockNondegenerate_of_mem_expand hxy⟩
  obtain ⟨cs, is, hg⟩ := exists_grouped ys
  let even := cs.filter (fun c => decide (c.parity = 0))
  let odd := cs.filter (fun c => !(decide (c.parity = 0)))
  let ds := is.mergeSort (fun d e => decide (e.weight.natAbs ≤ d.weight.natAbs))
  have hcperm : (even ++ odd).Perm cs := List.filter_append_perm _ cs
  have hdperm : ds.Perm is := List.mergeSort_perm _ _
  have hdord : ds.Pairwise (fun d e => e.weight.natAbs ≤ d.weight.natAbs) := by
    have h := List.pairwise_mergeSort (le := fun d e : ComplexCharacterData =>
        decide (e.weight.natAbs ≤ d.weight.natAbs))
      (fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
      (fun d e => by simpa using le_total e.weight.natAbs d.weight.natAbs) is
    exact h.imp fun h₁ => of_decide_eq_true h₁
  have hcs (c : RealCharacterData) (hc : c ∈ cs) : c.exponent.re = r := by
    exact (hys (.character c) (hg.mem_iff.mpr
      (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)))).1
  have hds (d : ComplexCharacterData) (hd : d ∈ ds) :
      d.exponent.re = r ∧ d.weight ≠ 0 :=
    hys (.induced d) (hg.mem_iff.mpr
      (List.mem_append_right _ (List.mem_map.mpr ⟨d, hdperm.subset hd, rfl⟩)))
  let pre := even.map RealBlock.character
  let post := odd.map RealBlock.character
  let zs := pre ++ ds.reverse.map RealBlock.induced ++ post
  have hzperm : zs.Perm ys := by
    have h1 : zs.Perm ((even ++ odd).map RealBlock.character ++ ds.reverse.map RealBlock.induced) := by
      simpa only [zs, pre, post, List.map_append, List.append_assoc] using
        (List.perm_append_comm (l₁ := ds.reverse.map RealBlock.induced) (l₂ := post))
          |>.append_left pre
    have h2 := (hcperm.map RealBlock.character).append
      (((List.reverse_perm ds).trans hdperm).map RealBlock.induced)
    exact h1.trans (h2.trans hg.symm)
  have hzRank : realRank zs = n := (realRank_perm hzperm).trans hysRank
  have hyz := RealTiedScalarAssembly.realInjectiveIntertwinerExists_perm hzperm.symm [] hysRank
    (fun y hy => (hys y hy).1)
  have hzy := RealTiedScalarAssembly.realInjectiveIntertwinerExists_perm hzperm [] hzRank
    (fun z hz => (hys z (hzperm.subset hz)).1)
  have hyz' : RealInjectiveIntertwinerExists n ys zs := by simpa only [List.nil_append] using hyz
  have hzy' : RealInjectiveIntertwinerExists n zs ys := by simpa only [List.nil_append] using hzy
  have hn' : realRank ((donorChars even ds odd).map RealBlock.character) = n := by
    rw [realRank_perm ((donorChars_perm_receiverChars even ds odd).map RealBlock.character)]
    rw [receiverChars, List.map_append, List.map_append]
    change realRank (pre ++ (splitChars ds.reverse).map RealBlock.character ++ post) = n
    simpa only [zs, realRank_append, split_rank] using hzRank
  have hQ := nested_surjection (r := r) ds pre post
    (by simpa only [donorChars, List.map_append] using hn')
    (fun d hd => (hds d hd).2) (fun d hd => (hds d hd).1) hdord
  have hJ := split_injection ds.reverse pre post hzRank
    (fun d hd => (hds d (List.mem_reverse.mp hd)).2)
  have hQ' : RealSurjectiveIntertwinerExists n
      ((donorChars even ds odd).map RealBlock.character) zs := by
    simpa only [donorChars, List.map_append] using hQ
  have hJ' : RealInjectiveIntertwinerExists n zs ((receiverChars even ds odd).map RealBlock.character) := by
    simpa only [receiverChars, List.map_append] using hJ
  refine ⟨even, odd, ds, ?_, ?_, fun d hd => ⟨(hds d hd).1, Int.natAbs_pos.mpr (hds d hd).2⟩,
    hdord, (realRank_map_character _).symm.trans hn',
    hQ'.trans ((surjection_of_two_injections hzy' hyz').trans
      (RealSurjectiveIntertwinerExists.of_eq hysMod.symm)),
    (hyz'.trans hJ').of_eq hysMod.symm rfl⟩
  · intro c hc
    simp only [even, List.mem_filter, decide_eq_true_eq] at hc
    exact ⟨hcs c hc.1, hc.2⟩
  · intro c hc
    simp only [odd, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    refine ⟨hcs c hc.1, Fin.ext ?_⟩
    have h0 : c.parity.val ≠ 0 := fun h => hc.2 (Fin.ext h)
    have h2 := c.parity.isLt
    omega

end Langlands.Archimedean.RealDiscreteNestedAssembly
