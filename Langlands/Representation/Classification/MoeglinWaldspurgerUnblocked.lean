import Langlands.Representation.Classification.MoeglinWaldspurgerHeadRealization

/-!
# The unblocked case of the derivative facts

For a multisegment `b` all of whose occurrences end at `c` or `c - 1`, and in which no
occurrence ending at `c - 1` precedes an occurrence ending at `c`, all occurrences ending at `c`
are unmatched, and the Langlands head of `b` has highest left `ν^{x+c} ρ`-derivative
`(number of occurrences ending at c, Langlands head of the left derivative of b)`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

/-! ### Combinatorics -/

theorem unmatchedScan_noEnd (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ), (∀ J ∈ l, J.ending ≠ x) → unmatchedScan x l pool = []
  | [], _, _ => rfl
  | J :: l, pool, h => by
    have hJ := h J List.mem_cons_self
    have hl : ∀ K ∈ l, K.ending ≠ x := fun K hK => h K (List.mem_cons_of_mem _ hK)
    rw [unmatchedScan]
    by_cases h1 : J.ending = x - 1
    · rw [ite_eq_left h1]
      exact unmatchedScan_noEnd x l _ hl
    · rw [ite_eq_right h1, ite_eq_right hJ]
      exact unmatchedScan_noEnd x l _ hl

theorem unmatchedScan_unblocked (x : ℤ) :
    ∀ (l : List Interval), l.Pairwise (fun I J => ¬ (I.ending = x - 1 ∧ J.ending = x)) →
      unmatchedScan x l 0 = l.filter (fun I => decide (I.ending = x))
  | [], _ => rfl
  | J :: l, h => by
    obtain ⟨hJ, hl⟩ := List.pairwise_cons.mp h
    rw [unmatchedScan]
    by_cases h1 : J.ending = x - 1
    · have hno : ∀ K ∈ l, K.ending ≠ x := fun K hK hK' => hJ K hK ⟨h1, hK'⟩
      have hne : ¬ J.ending = x := by omega
      rw [ite_eq_left h1, List.filter_cons_of_neg (by simpa using hne), unmatchedScan_noEnd x l _ hno,
        eq_comm, List.filter_eq_nil_iff]
      intro K hK
      simpa using hno K hK
    · by_cases h2 : J.ending = x
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left rfl, List.filter_cons_of_pos (by simpa using h2),
          unmatchedScan_unblocked x l hl]
      · rw [ite_eq_right h1, ite_eq_right h2, List.filter_cons_of_neg (by simpa using h2)]
        exact unmatchedScan_unblocked x l hl

/-- Without blocking, every occurrence ending at `c` is unmatched. -/
theorem unmatched_of_unblocked (b : Multisegment) (c : ℤ) (hu : Unblocked b c) :
    unmatched b c = b.filter (fun I => I.ending = c) := by
  unfold unmatched
  rw [unmatchedScan_unblocked c _ ?_]
  · rw [← Multiset.filter_coe, Multiset.sort_eq]
  · refine (Multiset.pairwise_sort b ScanLE).imp_of_mem ?_
    intro I J hI hJ hIJ ⟨hIe, hJe⟩
    rw [Multiset.mem_sort] at hI hJ
    have := hu J hJ hJe I hI hIe
    unfold ScanLE at hIJ
    omega

/-- Shorten every interval of a list at its right end, as a multiset. -/
theorem coe_shortList : ∀ (l : List Interval),
    ((shortList l : List Interval) : Multisegment) = shorten (l : Multisegment)
  | [] => rfl
  | I :: l => by
    rw [← Multiset.cons_coe, shorten, Multiset.cons_bind, ← shorten, ← coe_shortList l]
    rw [show shortList (I :: l) = if h : I.beginning < I.ending then shortR I h :: shortList l
      else shortList l from rfl]
    unfold Interval.dropLast
    by_cases h : I.beginning < I.ending
    · rw [dite_eq_left h, dite_eq_left h, ← Multiset.cons_coe, Multiset.singleton_add]
      rfl
    · rw [dite_eq_right h, dite_eq_right h, zero_add]

theorem mem_shortList_ending (c : ℤ) : ∀ (l : List Interval), (∀ I ∈ l, I.ending = c) →
    ∀ J ∈ shortList l, J.ending = c - 1
  | [], _, _, hJ => by simp [shortList] at hJ
  | I :: l, h, J, hJ => by
    have hI := h I List.mem_cons_self
    have hl : ∀ K ∈ l, K.ending = c := fun K hK => h K (List.mem_cons_of_mem _ hK)
    unfold shortList at hJ
    split_ifs at hJ with hb
    · rcases List.mem_cons.mp hJ with rfl | hJ
      · show I.ending - 1 = c - 1
        omega
      · exact mem_shortList_ending c l hl J hJ
    · exact mem_shortList_ending c l hl J hJ

theorem pairwise_noPrec_of_ending (e : ℤ) (l : List Interval) (h : ∀ I ∈ l, I.ending = e) :
    l.Pairwise NoPrec :=
  List.pairwise_of_forall_mem_list fun I hI J hJ => by
    unfold NoPrec
    have := h I hI
    have := h J hJ
    omega

/-! ### The derivative of the Langlands head -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- **The unblocked case.** If every occurrence of `b` ends at `c` or `c - 1` and no occurrence
ending at `c - 1` precedes one ending at `c`, the Langlands head of `b` has highest left
`ν^{x+c} ρ`-derivative given by the unmatched occurrences and the Langlands head of the left
derivative of `b`. -/
theorem unblocked_LDrel (hL : LeftCuspidalDerivativeLemma.{uF, uV})
    (hLS : LanglandsSubrepresentationRealization.{uF, uV})
    (b : Multisegment) (c : ℤ) (htwo : ∀ I ∈ b, TwoEnd c I) (hu : Unblocked b c)
    {n m : ℕ} (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m)
    (hb : HeadClass F T ρ x b n cls) (hS : HeadClass F T ρ x (leftDerivative b c) m S) :
    LDrel F T ρ x c cls (unmatched b c).card S := by
  let := T.topology
  let U := (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : List Interval, Cs = (b.filter (fun I => I.ending = c)).toList :=
    ⟨_, rfl⟩
  obtain ⟨Ds, hDsdef⟩ : ∃ Ds : List Interval, Ds = (b.filter (fun I => ¬ I.ending = c)).toList :=
    ⟨_, rfl⟩
  have hCs : ∀ I ∈ Cs, I.ending = c := by
    intro I hI
    rw [hCsdef, Multiset.mem_toList, Multiset.mem_filter] at hI
    exact hI.2
  have hDs : ∀ I ∈ Ds, I.ending = c - 1 := by
    intro I hI
    rw [hDsdef, Multiset.mem_toList, Multiset.mem_filter] at hI
    rcases htwo I hI.1 with h | h
    · exact absurd h hI.2
    · exact h
  have hbl : ((Cs ++ Ds : List Interval) : Multisegment) = b := by
    rw [← Multiset.coe_add, hCsdef, hDsdef, Multiset.coe_toList, Multiset.coe_toList,
      Multiset.filter_add_not]
  have hK : (unmatched b c).card = Cs.length := by
    rw [unmatched_of_unblocked b c hu, hCsdef, Multiset.length_toList]
  have hld : ((shortList Cs ++ Ds : List Interval) : Multisegment) = leftDerivative b c := by
    unfold leftDerivative
    rw [unmatched_of_unblocked b c hu, ← Multiset.coe_add, coe_shortList, hCsdef, hDsdef,
      Multiset.coe_toList, Multiset.coe_toList]
    have h1 : b.filter (fun I => I.ending = c) + b.filter (fun I => ¬ I.ending = c) = b :=
      Multiset.filter_add_not _ b
    have h2 : b - b.filter (fun I => I.ending = c) = b.filter (fun I => ¬ I.ending = c) := by
      calc b - b.filter (fun I => I.ending = c)
          = (b.filter (fun I => I.ending = c) + b.filter (fun I => ¬ I.ending = c)) -
              b.filter (fun I => I.ending = c) := by rw [h1]
        _ = b.filter (fun I => ¬ I.ending = c) := add_tsub_cancel_left _ _
    rw [h2, add_comm]
  -- the Langlands head embeds into the product of heads, `c`-enders first
  have hord₁ : (Cs ++ Ds).Pairwise NoPrec := by
    rw [List.pairwise_append]
    refine ⟨pairwise_noPrec_of_ending c Cs hCs, pairwise_noPrec_of_ending (c - 1) Ds hDs, ?_⟩
    intro I hI J hJ
    unfold NoPrec
    have hIc := hCs I hI
    have hJc := hDs J hJ
    have hIb : I ∈ b := by
      rw [hCsdef, Multiset.mem_toList, Multiset.mem_filter] at hI
      exact hI.1
    have hJb : J ∈ b := by
      rw [hDsdef, Multiset.mem_toList, Multiset.mem_filter] at hJ
      exact hJ.1
    have := hu I hIb hIc J hJb hJc
    omega
  obtain ⟨π, hπ, rfl, hhead⟩ := hb
  obtain ⟨hL₁, -⟩ := lsub_listProd.{uF, uV} ρ x hLS (Cs ++ Ds) hord₁
  have e₁ : Embeds T π (listProd F ρ x (Cs ++ Ds) U) := hL₁ π (hbl ▸ hhead)
  have e₂ := e₁.castIso_right (castIso_listProd_append.{uF, uV} ρ x Cs Ds U)
  have hU : PosOrIrr T U := empty_posOrIrr.{uF, uV}
  have hDU : PosOrIrr T (listProd F ρ x Ds U) := posOrIrr_listProd.{uF, uV} ρ x Ds U hU
  have e₃ := cut_listProd.{uF, uV} ρ x c Cs hCs (listProd F ρ x Ds U) hDU
  have e₄ := e₂.trans e₃
  -- the shortened product
  have hord₂ : (shortList Cs ++ Ds).Pairwise NoPrec := by
    refine pairwise_noPrec_of_ending (c - 1) _ ?_
    intro J hJ
    rcases List.mem_append.mp hJ with hJ | hJ
    · exact mem_shortList_ending c Cs hCs J hJ
    · exact hDs J hJ
  obtain ⟨hL₁', hL₂'⟩ := lsub_listProd.{uF, uV} ρ x hLS (shortList Cs ++ Ds) hord₂
  have hiso := castIso_listProd_append.{uF, uV} ρ x (shortList Cs) Ds U
  have hUf : U.HasFiniteLength := empty_hasFiniteLength.{uF, uV}
  have hDf := listProd_hasFiniteLength.{uF, uV} ρ x Ds U hUf
  have hYf := listProd_hasFiniteLength.{uF, uV} ρ x (shortList Cs) (listProd F ρ x Ds U) hDf
  have hUred : LeftReduced F T (cuspRep F T ρ x c) U := leftReduced_rankZero.{uF, uV} ρ.rank_pos _ U
  have hDred := listProd_leftReduced.{uF, uV} ρ x hL c Ds
    (fun J hJ h => by have := hDs J hJ; omega) U hUf hUred
  have hYred := listProd_leftReduced.{uF, uV} ρ x hL c (shortList Cs)
    (fun J hJ h => by have := mem_shortList_ending c Cs hCs J hJ; omega) _ hDf hDred
  have hex : ∃ D : SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (listRank ρ x (shortList Cs) (listRank ρ x Ds 0)) F.Carrier),
      D.IsIrreducible ∧ SmoothRep.IsSubrepresentation D
        (listProd F ρ x (shortList Cs) (listProd F ρ x Ds U)) := by
    obtain ⟨πS, hπS, -, hheadS⟩ := hS
    have eS := (hL₁' πS (hld ▸ hheadS)).castIso_right hiso
    obtain ⟨h, hsub⟩ := eS
    exact ⟨T.castRank h πS, T.isIrreducible_castRank h πS hπS, hsub⟩
  have hYhead : ∀ W : SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (listRank ρ x (shortList Cs) (listRank ρ x Ds 0)) F.Carrier),
      W.IsIrreducible → SmoothRep.IsSubrepresentation W
        (listProd F ρ x (shortList Cs) (listProd F ρ x Ds U)) →
        (realize ρ x (leftDerivative b c)).IsLanglandsHead W := by
    intro W hW hsub
    have eW := (embeds_of_isSubrepresentation hsub).castIso_right hiso.symm
    have := hL₂' W hW eW
    rwa [hld] at this
  rw [hK]
  exact LDrel_of_embeds_head.{uF, uV} ρ x hL c (leftDerivative b c) π hπ _ hYf hYred hex hYhead
    S hS e₄

end Langlands.MoeglinWaldspurger.Derivation
