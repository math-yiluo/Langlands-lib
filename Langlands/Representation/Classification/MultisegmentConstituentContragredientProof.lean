import Langlands.Representation.Classification.MultisegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.SegmentSocleContragredient
import Langlands.Representation.Classification.SegmentDualPrecedence
import Mathlib.Data.List.FinRange

/-! Smooth contragredient compatibility for actual multisegment constituents. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

variable {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)

/-- Reverse the segment family and take the actual smooth dual of every block. -/
def dualReverse : SegmentProductDatum.{uV, uF} T n where
  length := d.length
  segments i := (d.segments i.rev).dual
  degree_sum := (Equiv.sum_comp Fin.revPerm (fun i => (d.segments i).degree)).trans
    d.degree_sum
  blocks i :=
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (d.segments i.rev).degree
    (d.blocks i.rev).contragredient

/-- The reversed dual datum has exactly the reversed original block shape. -/
theorem dualReverse_shape : d.dualReverse.shape = d.shape.reverse := rfl

/-- The actual induced representation of the reversed dual datum. -/
theorem dualReverse_induced :
    letI := T.topology
    letI : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
      fun k => T.generalLinearTopologicalGroup k
    d.dualReverse.induced = (T.normalizedProductInductionFunctor d.shape.reverse).obj
      (fun i => (d.blocks i.rev).contragredient) := rfl

/-- Reversal changes the ordering, while the multiset simply maps segment duality. -/
theorem dualReverse_multisegment :
    d.dualReverse.multisegment = d.multisegment.map Segment.dual := by
  rw [multisegment, multisegment, Multiset.map_coe, List.map_ofFn]
  exact Multiset.coe_eq_coe.mpr
    (Fin.revPerm.ofFn_comp_perm (fun i => (d.segments i).dual))

/-- The reversed dual ordering is precedence-ordered whenever the original is. -/
theorem IsPrecedenceOrdered.dualReverse (h : d.IsPrecedenceOrdered) :
    d.dualReverse.IsPrecedenceOrdered := by
  intro i j hij hp
  exact h j.rev i.rev (Fin.rev_lt_rev.mpr hij)
    ((Segment.precedes_dual_iff _ _).mp hp)

/-- Each reversed dual block is the socle of the corresponding dual segment. -/
theorem HasSegmentSocles.dualReverse (h : d.HasSegmentSocles) :
    d.dualReverse.HasSegmentSocles := by
  intro i
  exact (h i.rev).contragredient

/-- Each reversed dual block is the head of the corresponding dual segment. -/
theorem HasSegmentHeads.dualReverse (h : d.HasSegmentHeads) :
    d.dualReverse.HasSegmentHeads := by
  intro i
  exact (h i.rev).contragredient

set_option maxHeartbeats 800000 in
/-- Smooth duality preserves the strong Zelevinsky socle for reversed dual data. -/
theorem IsZelevinskySocle.contragredient (hn : 0 < n)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySocle π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    d.dualReverse.IsZelevinskySocle π.contragredient := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  have hirr (i : Fin d.shape.length) :
      Representation.IsIrreducible (d.blocks i).representation :=
    (h.2.1 i).choose_spec.2.1
  refine ⟨h.1.dualReverse, h.2.1.dualReverse, ?_⟩
  change IsIrreducibleSocle d.dualReverse.induced.representation
    (smoothContragredient π.representation)
  rw [dualReverse_induced]
  erw [T.normalizedProductInductionFunctor_obj]
  simp only [SmoothRep.contragredient_representation]
  have hi := h.2.2
  rw [induced_representation] at hi
  exact IsIrreducibleSocle.contragredient_product T hn d.shape d.blocks hirr
    (π := π) hi

set_option maxHeartbeats 800000 in
/-- Smooth duality preserves the strong Langlands head for reversed dual data. -/
theorem IsLanglandsHead.contragredient (hn : 0 < n)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    d.dualReverse.IsLanglandsHead π.contragredient := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  have hirr (i : Fin d.shape.length) :
      Representation.IsIrreducible (d.blocks i).representation :=
    (h.2.1 i).choose_spec.2.1
  refine ⟨h.1.dualReverse, h.2.1.dualReverse, ?_⟩
  change IsIrreducibleHead d.dualReverse.induced.representation
    (smoothContragredient π.representation)
  rw [dualReverse_induced]
  erw [T.normalizedProductInductionFunctor_obj]
  simp only [SmoothRep.contragredient_representation]
  have hi := h.2.2
  rw [induced_representation] at hi
  exact IsIrreducibleHead.contragredient_product T hn d.shape d.blocks hirr
    (π := π) hi

end SegmentProductDatum

/-- Dualizing every segment preserves the actual multisegment socle relation. -/
theorem Multisegment.IsZelevinskySocle.contragredient {n : ℕ} (hn : 0 < n)
    {a : Multisegment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsZelevinskySocle π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Multisegment.IsZelevinskySocle (a.map Segment.dual) π.contragredient := by
  obtain ⟨d, hd, hπ⟩ := h
  exact ⟨d.dualReverse, d.dualReverse_multisegment.trans (congrArg _ hd),
    SegmentProductDatum.IsZelevinskySocle.contragredient d hn hπ⟩

/-- Dualizing every segment preserves the actual multisegment head relation. -/
theorem Multisegment.IsLanglandsHead.contragredient {n : ℕ} (hn : 0 < n)
    {a : Multisegment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : a.IsLanglandsHead π) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Multisegment.IsLanglandsHead (a.map Segment.dual) π.contragredient := by
  obtain ⟨d, hd, hπ⟩ := h
  exact ⟨d.dualReverse, d.dualReverse_multisegment.trans (congrArg _ hd),
    SegmentProductDatum.IsLanglandsHead.contragredient d hn hπ⟩

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual smooth contragredient carries both multisegment constituents to
those of the endpoint-reversed dual multisegment. -/
theorem multisegmentConstituentContragredientCompatibility :
    MultisegmentConstituentContragredientCompatibility.{uF, uV} F T := by
  let := T.topology
  let : ∀ k : ℕ, IsTopologicalGroup (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearTopologicalGroup k
  intro r Δ B hB
  refine ⟨fun i => dualRep T (B i), ?_, ?_⟩
  · intro i
    exact ⟨Representation.Equiv.refl _⟩
  · let Δv : Fin r → T.Segment.{uV, uF} := fun i =>
      { base :=
          { rank := (Δ i).rank
            rank_pos := (Δ i).rank_pos
            cls := (dualRep T (B i)).isoClass }
        length := (Δ i).length
        length_pos := (Δ i).length_pos }
    have hv (i : Fin r) : Δv i = (Δ i).dual := by
      have hb : (Δv i).base = dualDatum (Δ i).last := by
        exact congrArg (CuspidalDatum.mk (Δ i).rank (Δ i).rank_pos)
          (dualRep_represents (hB i))
      exact congrArg (fun ρ : T.CuspidalDatum.{uV, uF} =>
        (⟨ρ, (Δ i).length, (Δ i).length_pos⟩ : T.Segment.{uV, uF})) hb
    have hav : (List.ofFn Δv : Multiset (T.Segment.{uV, uF})) =
        (List.ofFn Δ : Multiset (T.Segment.{uV, uF})).map Segment.dual := by
      rw [Multiset.map_coe, List.map_ofFn]
      exact congrArg (fun f => (List.ofFn f : Multiset (T.Segment.{uV, uF})))
        (funext hv)
    dsimp only
    intro n hn π
    change (Multisegment.IsZelevinskySocle
        (List.ofFn Δ : Multiset (T.Segment.{uV, uF})) π →
        Multisegment.IsZelevinskySocle
          (List.ofFn Δv : Multiset (T.Segment.{uV, uF})) π.contragredient) ∧
      (Multisegment.IsLanglandsHead
        (List.ofFn Δ : Multiset (T.Segment.{uV, uF})) π →
        Multisegment.IsLanglandsHead
          (List.ofFn Δv : Multiset (T.Segment.{uV, uF})) π.contragredient)
    rw [hav]
    exact ⟨fun h => h.contragredient hn, fun h => h.contragredient hn⟩

end Langlands.Classification
