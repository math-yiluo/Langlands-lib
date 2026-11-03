import Langlands.Representation.Classification.TwoSegmentSocleCommutationStatement
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof

namespace Langlands

universe uK uG uA uB uF uV

/-- Irreducible actual representations with matching factors are equivalent. -/
theorem nonempty_equiv_of_isIrreducible_of_sameFactors
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G)
    (hA : Representation.IsIrreducible A.ρ)
    (hB : Representation.IsIrreducible B.ρ)
    (h : HaveSameJordanHolderFactors A B) : Nonempty (A.ρ.Equiv B.ρ) := by
  obtain ⟨n, s, t, hs, ht, e, he⟩ := h
  obtain ⟨a, ha, ⟨ea⟩⟩ := IrreducibleMultiplicityProof.compositionSeries k G A hA
  obtain ⟨b, hb, ⟨eb⟩⟩ := IrreducibleMultiplicityProof.compositionSeries k G B hB
  obtain ⟨f, hf⟩ := jordanHolderSeriesComparison k G A 1 n a s ha hs
  obtain ⟨g, hg⟩ := jordanHolderSeriesComparison k G B n 1 t b ht hb
  obtain ⟨u⟩ := hf 0
  obtain ⟨v⟩ := he (f 0)
  obtain ⟨w⟩ := hg (e (f 0))
  rw [Fin.fin_one_eq_zero (g (e (f 0)))] at w
  exact ⟨ea.symm.trans (u.trans (v.trans (w.trans eb)))⟩

namespace PadicField.TopologicalData.SegmentProductDatum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A two-entry datum of unlinked segments has an unlinked multisegment. -/
theorem isUnlinked_of_length_two {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (h₂ : d.length = 2)
    (hu : ¬ (d.segments ⟨0, by omega⟩).IsLinked (d.segments ⟨1, by omega⟩)) :
    d.multisegment.IsUnlinked := by
  intro Δ hΔ Γ hΓ
  obtain ⟨i, rfl⟩ : ∃ i, d.segments i = Δ := by
    simpa only [multisegment, Multiset.mem_coe, List.mem_ofFn] using hΔ
  obtain ⟨j, rfl⟩ : ∃ j, d.segments j = Γ := by
    simpa only [multisegment, Multiset.mem_coe, List.mem_ofFn] using hΓ
  have hi : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
    have := i.isLt
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hj : j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
    have := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact Segment.not_isLinked_self _
  · exact hu
  · exact fun h => hu h.symm
  · exact Segment.not_isLinked_self _

/-- A nonempty list of positive-degree segments has positive total rank. -/
theorem rank_pos_of_length_pos {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (h : 0 < d.length) : 0 < n := by
  rw [← d.degree_sum]
  exact Finset.sum_pos (fun i _ => (d.segments i).degree_pos)
    ⟨⟨0, h⟩, Finset.mem_univ _⟩

end PadicField.TopologicalData.SegmentProductDatum

namespace Classification

open CategoryTheory

/-- The normalized products of two supplied socles of unlinked segments are
isomorphic after swapping the two labels. -/
theorem twoSegmentSocleCommutation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSegmentSocleCommutation.{uF, uV} F T := by
  let := T.topology
  have hU := unlinkedSegmentSocleProductIrreducible.{uF, max uF uV} F T
  intro n d h₂ hs hu
  let σ := d.shape.adjacentSwap 0 (by change 0 + 1 < d.length; omega)
  have hn : 0 < n := d.rank_pos_of_length_pos (by omega)
  cases n with
  | zero => omega
  | succ m =>
    have hUnlinked := d.isUnlinked_of_length_two h₂ hu
    have hPermuted : (d.permute σ).multisegment.IsUnlinked := by
      have hm : (d.permute σ).multisegment = d.multisegment :=
        Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm d.segments)
      rw [hm]
      exact hUnlinked
    have h₁ := hU m d hs hUnlinked
    have h₂' := hU m (d.permute σ) (fun i => hs (σ i)) hPermuted
    have hBlocks : ∀ i, (d.blocks i).IsIrreducible := by
      intro i
      obtain ⟨A, hA, hπ⟩ := hs i
      exact hπ.1
    have hSame : HaveSameJordanHolderFactors
        (Rep.of d.induced.representation) (Rep.of (d.permute σ).induced.representation) :=
      twoFactorProductConstituentCommutativity.{uF, max uF uV} F T
        (m + 1) d.shape h₂ d.blocks hBlocks
    obtain ⟨e⟩ := nonempty_equiv_of_isIrreducible_of_sameFactors
      (Rep.of d.induced.representation) (Rep.of (d.permute σ).induced.representation)
      h₁ h₂' hSame
    exact ⟨SmoothRep.mkIso e⟩

end Classification

end Langlands
