import Langlands.Representation.Classification.MoeglinWaldspurgerUnblocked

/-!
# The inert part of the derivative facts

The derivative of the Langlands head of a multisegment `b` with respect to `ν^{x+c} ρ` is
computed from that of the Langlands head of its occurrences ending at `c` or `c - 1`: the other
occurrences are inert.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

/-! ### Sorting by endings -/

/-- The occurrences of `s`, sorted by increasing ending. -/
def sortE (s : Multisegment) : List Interval :=
  s.toList.mergeSort (fun I J => decide (I.ending ≤ J.ending))

theorem coe_sortE (s : Multisegment) : ((sortE s : List Interval) : Multisegment) = s := by
  unfold sortE
  conv_rhs => rw [← Multiset.coe_toList s]
  exact Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _)

theorem mem_sortE {s : Multisegment} {I : Interval} : I ∈ sortE s ↔ I ∈ s := by
  unfold sortE
  rw [List.mem_mergeSort, Multiset.mem_toList]

theorem sortE_pairwise (s : Multisegment) :
    (sortE s).Pairwise (fun I J => I.ending ≤ J.ending) := by
  have h := List.pairwise_mergeSort (le := fun I J : Interval => decide (I.ending ≤ J.ending))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) s.toList
  exact h.imp (fun hIJ => by simpa using hIJ)

theorem pairwise_noPrec_of_ending_le (l : List Interval)
    (h : l.Pairwise (fun I J => I.ending ≤ J.ending)) : l.Pairwise NoPrec :=
  h.imp (fun {I J} hIJ => by unfold NoPrec; omega)

theorem filter_notTwoEnd_eq (b : Multisegment) (c : ℤ) :
    b.filter (fun I => ¬ TwoEnd c I) =
      b.filter (fun I => I.ending + 1 < c) + b.filter (fun I => c < I.ending) := by
  rw [Multiset.filter_add_filter]
  have h0 : b.filter (fun I => I.ending + 1 < c ∧ c < I.ending) = 0 :=
    Multiset.filter_eq_nil.mpr (fun I _ h => by omega)
  rw [h0, add_zero]
  exact Multiset.filter_congr (fun I _ => by unfold TwoEnd; omega)

/-! ### Products along lists with a tail -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

theorem castIso_listProd_congr :
    ∀ (l : List Interval) {m m' : ℕ}
      {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
      {Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)},
      CastIso T Y Y' → CastIso T (listProd F ρ x l Y) (listProd F ρ x l Y')
  | [], _, _, _, _, h => h
  | I :: l, _, _, _, _, h => by
    let := T.topology
    have h' := castIso_listProd_congr l h
    exact (CastIso.refl (segHead F ρ x I)).binary h'

theorem embeds_listProd_congr :
    ∀ (l : List Interval) {m m' : ℕ}
      {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
      {Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)},
      Embeds T Y Y' → Embeds T (listProd F ρ x l Y) (listProd F ρ x l Y')
  | [], _, _, _, _, h => h
  | I :: l, _, _, _, _, h => by
    let := T.topology
    have h' := embeds_listProd_congr l h
    exact (CastIso.refl (segHead F ρ x I)).embeds.binary h'

theorem nontrivial_of_irr' {a : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hX : letI := T.topology; X.IsIrreducible) : letI := T.topology; Nontrivial X := by
  let := T.topology
  exact Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hX

/-- `(L(l) × 1) × H ≅ L(l) × H`: the empty tail is removed. -/
theorem castIso_listProd_unit (l : List Interval) {c : ℕ}
    (H : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier))
    (hH : PosOrIrr T H) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor (listRank ρ x l 0) c).obj
        (listProd F ρ x l
          (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced, H))
      (listProd F ρ x l H) := by
  let := T.topology
  have hU := empty_posOrIrr.{uF, uV} (T := T)
  have hUi := empty_isIrreducible.{uF, uV} (T := T)
  have h1 := castIso_listProd_binary.{uF, uV} ρ x l
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced H hU hH
  have h2 := castIso_rankZero_left.{uF, uV} rfl
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced hUi H
  have h3 := castIso_listProd_congr.{uF, uV} ρ x l h2
  exact h1.trans h3

/-- A Langlands head of `l` times `H` embeds into `L(l) × H`. -/
theorem embeds_head_binary (hLS : LanglandsSubrepresentationRealization.{uF, uV})
    (l : List Interval) (hl : l.Pairwise NoPrec) {k c : ℕ}
    (πh : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (hπh : (realize ρ x (l : Multisegment)).IsLanglandsHead πh)
    (H : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier))
    (hH : PosOrIrr T H) :
    letI := T.topology
    Embeds T ((T.binaryNormalizedProductFunctor k c).obj (πh, H)) (listProd F ρ x l H) := by
  let := T.topology
  have h1 := (lsub_listProd.{uF, uV} ρ x hLS l hl).1 πh hπh
  have h2 := h1.binary (CastIso.refl H).embeds
  have h3 := castIso_listProd_unit.{uF, uV} ρ x l H hH
  exact h2.castIso_right h3

/-! ### The inert occurrences -/

/-- **Inert occurrences.** The derivative data of the Langlands head of `b` with respect to
`ν^{x+c} ρ` are those of the Langlands head of its occurrences ending at `c` or `c - 1`, with
the remaining occurrences added to the derivative side. -/
theorem inert_LDrel (hL : LeftCuspidalDerivativeLemma.{uF, uV})
    (hLS : LanglandsSubrepresentationRealization.{uF, uV})
    (b : Multisegment) (c : ℤ) (δ : Multisegment) (hδ : ∀ I ∈ δ, TwoEnd c I)
    {n₀ m₀ n m : ℕ} (clsJ : Label.{uF, uV} F T n₀) (SJ : Label.{uF, uV} F T m₀)
    (cls : Label.{uF, uV} F T n) (S : Label.{uF, uV} F T m) (K : ℕ)
    (hJ : HeadClass F T ρ x (b.filter (TwoEnd c)) n₀ clsJ) (hδS : HeadClass F T ρ x δ m₀ SJ)
    (hLD : LDrel F T ρ x c clsJ K SJ) (hb : HeadClass F T ρ x b n cls)
    (hS : HeadClass F T ρ x (b.filter (fun I => ¬ TwoEnd c I) + δ) m S) :
    LDrel F T ρ x c cls K S := by
  let := T.topology
  let U := (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced
  let A := cuspRep F T ρ x c
  have hr : 0 < ρ.rank := ρ.rank_pos
  -- the lists
  obtain ⟨low, hlow⟩ : ∃ l, l = sortE (b.filter (fun I => I.ending + 1 < c)) := ⟨_, rfl⟩
  obtain ⟨Jl, hJl⟩ : ∃ l, l = sortE (b.filter (TwoEnd c)) := ⟨_, rfl⟩
  obtain ⟨high, hhigh⟩ : ∃ l, l = sortE (b.filter (fun I => c < I.ending)) := ⟨_, rfl⟩
  obtain ⟨δl, hδl⟩ : ∃ l, l = sortE δ := ⟨_, rfl⟩
  have hlowe : ∀ I ∈ low, I.ending + 1 < c := by
    intro I hI
    rw [hlow, mem_sortE, Multiset.mem_filter] at hI
    exact hI.2
  have hhighe : ∀ I ∈ high, c < I.ending := by
    intro I hI
    rw [hhigh, mem_sortE, Multiset.mem_filter] at hI
    exact hI.2
  have hJle : ∀ I ∈ Jl, TwoEnd c I := by
    intro I hI
    rw [hJl, mem_sortE, Multiset.mem_filter] at hI
    exact hI.2
  have hδle : ∀ I ∈ δl, TwoEnd c I := by
    intro I hI
    rw [hδl, mem_sortE] at hI
    exact hδ I hI
  have hord : ∀ M : List Interval, M.Pairwise (fun I J => I.ending ≤ J.ending) →
      (∀ I ∈ M, TwoEnd c I) → (low ++ (M ++ high)).Pairwise NoPrec := by
    intro M hM hMe
    apply pairwise_noPrec_of_ending_le
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨hlow ▸ sortE_pairwise _, ⟨hM, hhigh ▸ sortE_pairwise _, ?_⟩, ?_⟩
    · intro I hI J hJ
      have h1 := hMe I hI
      have h2 := hhighe J hJ
      unfold TwoEnd at h1
      omega
    · intro I hI J hJ
      have h1 := hlowe I hI
      rcases List.mem_append.mp hJ with hJ | hJ
      · have h2 := hMe J hJ
        unfold TwoEnd at h2
        omega
      · have h2 := hhighe J hJ
        omega
  have hJs : Jl.Pairwise (fun I J => I.ending ≤ J.ending) := hJl ▸ sortE_pairwise _
  have hδs : δl.Pairwise (fun I J => I.ending ≤ J.ending) := hδl ▸ sortE_pairwise _
  have hHs : high.Pairwise (fun I J => I.ending ≤ J.ending) := hhigh ▸ sortE_pairwise _
  -- the multisets
  have hbl : ((low ++ (Jl ++ high) : List Interval) : Multisegment) = b := by
    rw [← Multiset.coe_add, ← Multiset.coe_add, hlow, hJl, hhigh, coe_sortE, coe_sortE,
      coe_sortE, add_left_comm, ← filter_notTwoEnd_eq]
    exact Multiset.filter_add_not _ b
  have hβl : ((low ++ (δl ++ high) : List Interval) : Multisegment) =
      b.filter (fun I => ¬ TwoEnd c I) + δ := by
    rw [← Multiset.coe_add, ← Multiset.coe_add, hlow, hδl, hhigh, coe_sortE, coe_sortE,
      coe_sortE, filter_notTwoEnd_eq, add_comm δ, ← add_assoc]
  have hJlc : ((Jl : List Interval) : Multisegment) = b.filter (TwoEnd c) := by
    rw [hJl, coe_sortE]
  have hδlc : ((δl : List Interval) : Multisegment) = δ := by
    rw [hδl, coe_sortE]
  -- the tail `H` of heads of the occurrences ending above `c`
  have hU : PosOrIrr T U := empty_posOrIrr.{uF, uV}
  have hUf : U.HasFiniteLength := empty_hasFiniteLength.{uF, uV}
  have hUn : Nontrivial U := empty_nontrivial.{uF, uV}
  have hUred : LeftReduced F T A U := leftReduced_rankZero.{uF, uV} hr _ U
  have hH := posOrIrr_listProd.{uF, uV} ρ x high U hU
  have hHf := listProd_hasFiniteLength.{uF, uV} ρ x high U hUf
  have hHn := listProd_nontrivial.{uF, uV} ρ x high U hUn
  have hHred := listProd_leftReduced.{uF, uV} ρ x hL c high
    (fun I hI h => by have := hhighe I hI; omega) U hUf hUred
  -- the derivative data of the two-end part
  obtain ⟨π, hπ, rfl, hhead⟩ := hb
  obtain ⟨πJ, hπJ, hπJc, hJhead⟩ := hJ
  obtain ⟨πδ, hπδ, hπδc, hδhead⟩ := hδS
  obtain ⟨hK, π', hπ', DJ, hDJ, hπ'c, hDJc, hDJred, hsub'⟩ := hLD
  subst hK
  have eJ : πJ ≅ π' := ((SmoothRep.irreducibleIsoClass_eq_iff hπJ hπ').mp
    (hπJc.trans hπ'c.symm)).some
  have eδ : DJ ≅ πδ := ((SmoothRep.irreducibleIsoClass_eq_iff hDJ hπδ).mp
    (hDJc.trans hπδc.symm)).some
  have eπJ : Embeds T πJ (iterProd T A.obj K DJ) := by
    have h := hsub'
    rw [powerProduct_eq_iterProd] at h
    exact ⟨rfl, isSubrepresentation_of_iso_left eJ.symm h⟩
  -- `π` embeds into `L(low) × (π_J × H)`
  have hXf : (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (πJ, listProd F ρ x high U))).HasFiniteLength := by
    have h1 := SmoothRep.hasFiniteLength_of_isIrreducible hπJ
    have h2 := Aubert.binaryProduct_preservesFiniteLength F T _ _ πJ (listProd F ρ x high U) h1 hHf
    exact listProd_hasFiniteLength.{uF, uV} ρ x low _ h2
  have hXn : Nontrivial (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (πJ, listProd F ρ x high U))) := by
    have h1 := nontrivial_of_irr' hπJ
    have h2 := binary_nontrivial_of.{uF, uV} _ _ h1 hHn
    exact listProd_nontrivial.{uF, uV} ρ x low _ h2
  have eX : Embeds T (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (πJ, listProd F ρ x high U))) (listProd F ρ x (low ++ (Jl ++ high)) U) := by
    have h1 := embeds_head_binary.{uF, uV} ρ x hLS Jl (pairwise_noPrec_of_ending_le Jl hJs) πJ
      (hJlc ▸ hJhead) (listProd F ρ x high U) hH
    have h2 := embeds_listProd_congr.{uF, uV} ρ x low h1
    have h3 := castIso_listProd_congr.{uF, uV} ρ x low
      (castIso_listProd_append.{uF, uV} ρ x Jl high U).symm
    have h4 := (castIso_listProd_append.{uF, uV} ρ x low (Jl ++ high) U).symm
    exact (h2.castIso_right h3).castIso_right h4
  obtain ⟨W, hW, j, hj⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hXf
  have hWhead : (realize ρ x b).IsLanglandsHead W := by
    have h1 := (lsub_listProd.{uF, uV} ρ x hLS (low ++ (Jl ++ high)) (hord Jl hJs hJle)).2 W hW
      ((embeds_of_isSubrepresentation ⟨j, hj⟩).trans eX)
    rwa [hbl] at h1
  have hrank := (langlandsHead_degree hWhead).symm.trans (langlandsHead_degree hhead)
  subst hrank
  have eW : Nonempty (W ≅ π) :=
    (Classification.multisegmentHeadClassification.{uF, uV} F T _ _ _ W π hWhead hhead).mp rfl
  have eπX : Embeds T π (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (πJ, listProd F ρ x high U))) :=
    ⟨rfl, isSubrepresentation_of_iso_left eW.some ⟨j, hj⟩⟩
  -- push the cuspidal factors to the left
  have hDJp := posOrIrr_of_isIrreducible hDJ
  have hY := posOrIrr_binary hDJp hH
  have f1 := embeds_listProd_congr.{uF, uV} ρ x low (eπJ.binary (CastIso.refl
    (listProd F ρ x high U)).embeds)
  have f2 := castIso_listProd_congr.{uF, uV} ρ x low
    (castIso_iterProd_binary hr A.obj K DJ (listProd F ρ x high U) hDJp hH)
  have f3 := castIso_listProd_iterProd.{uF, uV} ρ x c K low hlowe _ hY
  have hemb := eπX.trans ((f1.castIso_right f2).castIso_right f3)
  -- the derivative side
  have hDJf := SmoothRep.hasFiniteLength_of_isIrreducible hDJ
  have hYf₀ := Aubert.binaryProduct_preservesFiniteLength F T _ _ DJ (listProd F ρ x high U)
    hDJf hHf
  have hYf := listProd_hasFiniteLength.{uF, uV} ρ x low _ hYf₀
  obtain ⟨-, hprod, -, -, -⟩ := hL p F T ρ.rank A
  have hYred₀ := hprod _ _ DJ (listProd F ρ x high U) hDJf hHf hDJred hHred
  have hYred := listProd_leftReduced.{uF, uV} ρ x hL c low
    (fun I hI h => by have := hlowe I hI; omega) _ hYf₀ hYred₀
  have hYn : Nontrivial (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (DJ, listProd F ρ x high U))) := by
    have h1 := nontrivial_of_irr' hDJ
    have h2 := binary_nontrivial_of.{uF, uV} _ _ h1 hHn
    exact listProd_nontrivial.{uF, uV} ρ x low _ h2
  have hex : ∃ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
      (listRank ρ x low (m₀ + listRank ρ x high 0)) F.Carrier),
      D.IsIrreducible ∧ SmoothRep.IsSubrepresentation D
        (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
          (DJ, listProd F ρ x high U))) := by
    obtain ⟨D, hD, jD, hjD⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hYf
    exact ⟨D, hD, jD, hjD⟩
  have eY : Embeds T (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
      (DJ, listProd F ρ x high U))) (listProd F ρ x (low ++ (δl ++ high)) U) := by
    have h0 : CastIso T ((T.binaryNormalizedProductFunctor _ _).obj (DJ, listProd F ρ x high U))
        ((T.binaryNormalizedProductFunctor _ _).obj (πδ, listProd F ρ x high U)) :=
      (castIso_of_iso eδ).binary (CastIso.refl _)
    have h1 := embeds_head_binary.{uF, uV} ρ x hLS δl (pairwise_noPrec_of_ending_le δl hδs) πδ
      (hδlc ▸ hδhead) (listProd F ρ x high U) hH
    have h2 := embeds_listProd_congr.{uF, uV} ρ x low (h0.embeds.trans h1)
    have h3 := castIso_listProd_congr.{uF, uV} ρ x low
      (castIso_listProd_append.{uF, uV} ρ x δl high U).symm
    have h4 := (castIso_listProd_append.{uF, uV} ρ x low (δl ++ high) U).symm
    exact (h2.castIso_right h3).castIso_right h4
  have hYhead : ∀ W' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
      (listRank ρ x low (m₀ + listRank ρ x high 0)) F.Carrier),
      W'.IsIrreducible → SmoothRep.IsSubrepresentation W'
        (listProd F ρ x low ((T.binaryNormalizedProductFunctor _ _).obj
          (DJ, listProd F ρ x high U))) →
        (realize ρ x (b.filter (fun I => ¬ TwoEnd c I) + δ)).IsLanglandsHead W' := by
    intro W' hW' hsub
    have h1 := (lsub_listProd.{uF, uV} ρ x hLS (low ++ (δl ++ high)) (hord δl hδs hδle)).2 W' hW'
      ((embeds_of_isSubrepresentation hsub).trans eY)
    rwa [hβl] at h1
  exact LDrel_of_embeds_head.{uF, uV} ρ x hL c _ π hπ _ hYf hYred hex hYhead S hS hemb

end Langlands.MoeglinWaldspurger.Derivation
