import Langlands.Representation.Classification.A6iiAssembly

/-!
# Tadić's Corollary A.6(ii): irreducible products of Langlands heads

If `π_i` is a Langlands head of `a_i` for each block of `B` and the normalized
product of the `π_i` is irreducible, the product is a Langlands head of `∑ a_i`
(Tadić 1986, Corollary A.6(ii), for finitely many factors).
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData A6ii

universe uF uV

variable {p : ℕ} [Fact p.Prime]

namespace A6ii

set_option maxHeartbeats 2000000 in
/-- Positive rank: a product of heads of decreasingly sorted segment data, when
irreducible, is the Langlands head of the merged datum. -/
theorem positiveRank (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (hn : 0 < n)
    (B : BlockShape n) (d' : ∀ i, T.SegmentProductDatum.{max uF uV, uF} (B.size i))
    (hh : ∀ i, (d' i).HasSegmentHeads)
    (u : letI := T.topology
      ∀ i j, UnitaryExponentData (T.determinantNorm ((d' i).segments j).degree)
        ((d' i).blocks j).representation)
    (hanti : ∀ i, Antitone (fun j => (u i j).exponent))
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hπ : letI := T.topology
      ∀ i, IsIrreducibleHead (d' i).induced.representation (π i).representation)
    (hirr : letI := T.topology
      Representation.IsIrreducible ((T.normalizedProductInductionFunctor B).obj π).representation) :
    letI := T.topology
    ∃ dc : T.SegmentProductDatum.{max uF uV, uF} n,
      dc.multisegment = (SegmentProductDatum.concatenate B d').multisegment ∧
        dc.IsLanglandsHead ((T.normalizedProductInductionFunctor B).obj π) := by
  let := T.topology
  let c := SegmentProductDatum.concatenate B d'
  have hhc : c.HasSegmentHeads := concatenate_hasSegmentHeads B d' hh
  let uc : ∀ l, UnitaryExponentData (T.determinantNorm (c.segments l).degree)
      (c.blocks l).representation :=
    fun l => u (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2
  let ex : Fin c.length → ℝ := fun l => (uc l).exponent
  have hexc : ∀ x : (i : Fin B.length) × Fin (d' i).length,
      ex (finSigmaFinEquiv x) = (u x.1 x.2).exponent := by
    intro x
    change (u (finSigmaFinEquiv.symm (finSigmaFinEquiv x)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv x)).2).exponent = _
    rw [Equiv.symm_apply_apply]
  have hantiG : ∀ i, Antitone (fun s : Fin (d' i).length => ex (finSigmaFinEquiv ⟨i, s⟩)) := by
    intro i s s' hss
    change ex (finSigmaFinEquiv ⟨i, s'⟩) ≤ ex (finSigmaFinEquiv ⟨i, s⟩)
    rw [hexc ⟨i, s'⟩, hexc ⟨i, s⟩]
    exact hanti i hss
  obtain ⟨m⟩ := exists_mergeGrouping (fun l => (c.segments l).degree)
    (fun l => (c.segments l).degree_pos) c.degree_sum ex
  have hodc : (merged c m).IsPrecedenceOrdered :=
    merged_isPrecedenceOrdered F T c m hhc uc (fun l => rfl)
  have hhdc : (merged c m).HasSegmentHeads := merged_hasSegmentHeads c m hhc
  obtain ⟨L, -, -, hLh⟩ := orderedMultisegmentHeadExistence.{uF, uV} F T n (merged c m) hodc hhdc
  obtain ⟨hL, qL0, hqL0, -⟩ := id hLh
  -- supercuspidal representatives of the segments
  have hA := fun q : (i : Fin B.length) × Fin (d' i).length => hh q.1 q.2
  choose A' hrep hA'h using hA
  have hA' : ∀ q : (i : Fin B.length) × Fin (d' i).length,
      IsIrreducibleQuotient
        (T.segmentInduced (A' q).obj ((d' q.1).segments q.2).length
          ((d' q.1).segments q.2).rank_pos).representation
        ((d' q.1).blocks q.2).representation :=
    fun q => ⟨(hA'h q).1, (hA'h q).2.choose, (hA'h q).2.choose_spec.1⟩
  have hsq : ∀ l, T.IsSquareIntegrable
      (T.segmentFactor (c.blocks l) (-(uc l).exponent)).representation := fun l =>
    chosenUnitarySquareIntegrability.{uF, uV} F T (c.segments l).degree
      (c.segments l).degree_pos (c.blocks l) (hhc l).choose_spec.2.1
      (exists_unitaryExponent.{uF, uV} F T c hhc l).1 (uc l)
  -- the Silberger side
  obtain ⟨m₀, hm₀, hIm, c', hc', hLm⟩ := silbergerSide.{uF, uV} F T hn c m
    (fun l => A' (finSigmaFinEquiv.symm l)) (fun l => hA' _) uc (fun l => rfl) hsq L hL
    (SmoothRep.ofHom qL0) hqL0
  -- the geometric side
  have hπi : ∀ i, Representation.IsIrreducible (π i).representation := fun i => (hπ i).1
  have hπa : ∀ i, IsAdmissible (π i).representation := fun i =>
    (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T _ (π i) (hπi i)).1
  have hqd := fun i => (hπ i).2
  choose qd0 hqd0 using hqd
  obtain ⟨k, hk, hPc⟩ := geometricSide.{uF, uV} F T hn B d' A' hA' π hπi hπa
    (fun i => SmoothRep.ofHom (qd0 i)) (fun i => (hqd0 i).1) hirr hantiG m
  -- the Jordan-Hölder comparison
  obtain ⟨hX, hI, hXI⟩ := jhComparison.{uF, uV} F T hn B d' hh m
  have hr := productMap_surjective F T B (fun i => SmoothRep.ofHom (qd0 i)) (fun i => (hqd0 i).1)
  -- the head-detecting count
  rw [← CuspidalJacquetMultiplicity.oppositeFunctor_obj] at hIm hLm hPc
  obtain ⟨e⟩ := HeadDetectingCount.nonempty_iso_of_count
    (CuspidalJacquetMultiplicity.oppositeFunctor T (fineShape c m))
    (oppositeFunctor_map_injective T _) (oppositeFunctor_map_surjective T _)
    hX hI hXI (SmoothRep.ofHom qL0) hqL0 hL _ hr hirr _ m₀ hIm ⟨c', hc', hLm⟩ ⟨k, hk, hPc⟩
  exact ⟨merged c m, merged_multisegment c m, hodc, hhdc,
    hLh.of_targetEquiv (SmoothRep.equivOfIso e.symm)⟩

/-- Rank zero: the empty product is the Langlands head of the empty multisegment. -/
theorem rankZero (F : PadicField.{uF} p) (T : F.TopologicalData) (B : BlockShape 0)
    (d : ∀ i, T.SegmentProductDatum.{max uF uV, uF} (B.size i))
    (hh : ∀ i, (d i).HasSegmentHeads)
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hirr : letI := T.topology
      Representation.IsIrreducible ((T.normalizedProductInductionFunctor B).obj π).representation) :
    letI := T.topology
    (SegmentProductDatum.concatenate B d).IsLanglandsHead
      ((T.normalizedProductInductionFunctor B).obj π) := by
  let := T.topology
  have hB : B.length = 0 := by
    by_contra h
    let i : Fin B.length := ⟨0, Nat.pos_of_ne_zero h⟩
    have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (B.size j)) (Finset.mem_univ i)
    rw [B.sum_eq] at hle
    exact absurd (B.positive i) (by omega)
  have hlen : (SegmentProductDatum.concatenate B d).length = 0 := by
    change ∑ k, (d k).length = 0
    exact Finset.sum_eq_zero fun k _ => (Nat.not_lt_zero _ (lt_of_lt_of_eq k.isLt hB)).elim
  refine ⟨fun i => (Nat.not_lt_zero _ (lt_of_lt_of_eq i.isLt hlen)).elim,
    concatenate_hasSegmentHeads B d hh, ?_⟩
  exact (isIrreducibleHead_self _ hirr).of_equiv
    (rankZeroEquiv F T B (SegmentProductDatum.concatenate B d).shape
      (fun i => (π i).representation)
      (fun l => ((SegmentProductDatum.concatenate B d).blocks l).representation))

end A6ii

set_option maxHeartbeats 1000000 in
/-- Tadić 1986, Corollary A.6(ii), for finitely many factors: an irreducible
normalized product of Langlands heads of `a_i` is a Langlands head of `∑ a_i`. -/
theorem irreducibleLanglandsHeadProduct (F : PadicField.{uF} p) (T : F.TopologicalData) :
    IrreducibleLanglandsHeadProduct.{uF, uV} F T := by
  let := T.topology
  intro n B a π hhead hirr
  choose d hdm hdl using hhead
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨SegmentProductDatum.concatenate B d, ?_,
      A6ii.rankZero.{uF, uV} F T B d (fun i => (hdl i).2.1) π hirr⟩
    rw [concatenate_multisegment]
    exact Finset.sum_congr rfl fun i _ => hdm i
  have hsort := fun i => exists_sorted.{uF, uV} F T (d i) (hdl i).1 (hdl i).2.1
  choose d' u hm' hh' hanti hiso using hsort
  have hπ : ∀ i, IsIrreducibleHead (d' i).induced.representation (π i).representation :=
    fun i => (hdl i).2.2.of_equiv (SmoothRep.equivOfIso (hiso i).some)
  obtain ⟨dc, hdcm, hdch⟩ := A6ii.positiveRank.{uF, uV} F T hn B d' hh' u hanti π hπ hirr
  refine ⟨dc, ?_, hdch⟩
  rw [hdcm, concatenate_multisegment]
  exact Finset.sum_congr rfl fun i _ => (hm' i).trans (hdm i)

end Langlands.Classification
