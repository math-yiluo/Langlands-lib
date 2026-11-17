import Langlands.Representation.Archimedean.RealCharacterInducedUnlinked
import Langlands.Representation.Archimedean.RealInducedCharacterUnlinked
import Langlands.Representation.Archimedean.RealInducedPairWeightZero
import Langlands.Representation.Archimedean.RealInducedPairKTypeTransport

/-!
# Unlinked exchange with one induction block of weight zero

Expanding the block of weight zero reduces its exchange to two published mixed
swaps. Compact type counting makes the resulting GL4 map bijective, giving the
one-piece adjacent filtration in the opposite order.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration

set_option backward.isDefEq.respectTransparency false

namespace RealInducedPairSingleZero

open RealInducedPairWeightZero

private theorem expand_eq (d : ComplexCharacterData) (hd : d.weight = 0) :
    realBlockExpand (.induced d) = [.character (first d), .character (second d)] := by
  simp [realBlockExpand, hd, first, second]

/-- Move a block of weight zero past an unlinked block of nonzero weight,
inside arbitrary surrounding lists, in descending exponent order. -/
theorem injective_zero_left (n : ℕ) (pre post : List RealBlock)
    (d e : ComplexCharacterData) (hd : d.weight = 0) (he : e.weight ≠ 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hord : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e)) :
    RealInjectiveIntertwinerExists n
      (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  have hfirst : AreRealBlocksUnlinked (.character (first d)) (.induced e) :=
    areRealBlocksUnlinked_of_mem_expand hun
      (by simp [expand_eq d hd]) (by simp [realBlockExpand, he])
  have hsecond : AreRealBlocksUnlinked (.character (second d)) (.induced e) :=
    areRealBlocksUnlinked_of_mem_expand hun
      (by simp [expand_eq d hd]) (by simp [realBlockExpand, he])
  have h1 := realCharacterInducedSwap n (pre ++ [.character (first d)]) post
    (second d) e he (by
      simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega) hord hsecond
  have h2 := realCharacterInducedSwap n pre (.character (second d) :: post)
    (first d) e he (by
      simp only [realRank, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, RealBlock.rank] at hrank ⊢
      omega) hord hfirst
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1
  refine (h1.trans h2).of_eq ?_ ?_
  · have h := realStandardModule_append_expand n pre (.induced e :: post) (.induced d)
    rw [expand_eq d hd] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    exact h.symm
  · have h := realStandardModule_append_expand n (pre ++ [.induced e]) post (.induced d)
    rw [expand_eq d hd] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    exact h.symm

/-- Move a block of nonzero weight past an unlinked block of weight zero,
inside arbitrary surrounding lists, in descending exponent order. -/
theorem injective_zero_right (n : ℕ) (pre post : List RealBlock)
    (d e : ComplexCharacterData) (hd : d.weight ≠ 0) (he : e.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hord : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e)) :
    RealInjectiveIntertwinerExists n
      (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  have hfirst : AreRealBlocksUnlinked (.induced d) (.character (first e)) :=
    areRealBlocksUnlinked_of_mem_expand hun
      (by simp [realBlockExpand, hd]) (by simp [expand_eq e he])
  have hsecond : AreRealBlocksUnlinked (.induced d) (.character (second e)) :=
    areRealBlocksUnlinked_of_mem_expand hun
      (by simp [realBlockExpand, hd]) (by simp [expand_eq e he])
  have h1 := realInducedCharacterSwap n pre (.character (second e) :: post)
    d (first e) hd (by
      simp only [realRank, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, RealBlock.rank] at hrank ⊢
      omega) hord hfirst
  have h2 := realInducedCharacterSwap n (pre ++ [.character (first e)]) post
    d (second e) hd (by
      simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega) hord hsecond
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h2
  refine (h1.trans h2).of_eq ?_ ?_
  · have h := realStandardModule_append_expand n (pre ++ [.induced d]) post (.induced e)
    rw [expand_eq e he] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    exact h.symm
  · have h := realStandardModule_append_expand n pre (.induced d :: post) (.induced e)
    rw [expand_eq e he] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    exact h.symm

/-- Exactly one zero weight suffices for a bijective exact GL4 exchange
of unlinked blocks in descending exponent order. -/
theorem exists_bijective_intertwiner (d e : ComplexCharacterData)
    (hz : (d.weight = 0 ∧ e.weight ≠ 0) ∨ (d.weight ≠ 0 ∧ e.weight = 0))
    (hord : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e)) :
    ∃ T : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 [.induced e, .induced d],
      IsRealIntertwinerModulo 4 [.induced d, .induced e] [.induced e, .induced d] ⊥ T ∧
        Function.Bijective T := by
  have hi : RealInjectiveIntertwinerExists 4 [.induced d, .induced e]
      [.induced e, .induced d] := by
    rcases hz with ⟨hd, he⟩ | ⟨hd, he⟩
    · exact injective_zero_left 4 [] [] d e hd he rfl hord hun
    · exact injective_zero_right 4 [] [] d e hd he rfl hord hun
  obtain ⟨T, hTi, hT⟩ := hi
  have hTm : IsRealIntertwinerModulo 4 [.induced d, .induced e]
      [.induced e, .induced d] ⊥ T :=
    InductionStages.isRealIntertwinerModulo_iff.mpr (by
      simpa only [Submodule.mem_bot, sub_eq_zero] using
        InductionStages.isRealStandardIntertwiner_iff.mp hT)
  exact ⟨T, hTm, hTi, RealInducedPairKTypeTransport.surjective_of_injective d e
    hTm.isRealKEquivariant hTi⟩

/-- For an ascending unlinked pair with exactly one zero weight, the
descending exchange map gives a one-piece adjacent filtration. -/
theorem filtration (d e : ComplexCharacterData)
    (hz : (d.weight = 0 ∧ e.weight ≠ 0) ∨ (d.weight ≠ 0 ∧ e.weight = 0))
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e))
    (hun : AreRealBlocksUnlinked (.induced e) (.induced d)) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hz' : (e.weight = 0 ∧ d.weight ≠ 0) ∨ (e.weight ≠ 0 ∧ d.weight = 0) := by
    rcases hz with ⟨hd, he⟩ | ⟨hd, he⟩
    · exact Or.inr ⟨he, hd⟩
    · exact Or.inl ⟨he, hd⟩
  obtain ⟨T, hT, hTb⟩ := exists_bijective_intertwiner e d hz' hlt.le hun
  refine (realAdjacentFiltration_iff 4 [] [] _ _).mpr ?_
  refine ((HasFiltration.self (n := 4)
    (P := fun es => es = [.induced e, .induced d]) rfl).map T hT hTb.2).mono ?_
  rintro es rfl
  exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩

end RealInducedPairSingleZero

/-- The unlinked adjacent filtration when exactly one induction weight is zero. -/
def RealInducedPairSingleZeroUnlinkedFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData,
    ((d.weight = 0 ∧ e.weight ≠ 0) ∨ (d.weight ≠ 0 ∧ e.weight = 0)) →
      realBlockExponent (.induced d) < realBlockExponent (.induced e) →
        AreRealBlocksUnlinked (.induced e) (.induced d) →
          RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairSingleZeroUnlinkedFiltration :
    RealInducedPairSingleZeroUnlinkedFiltrationStatement :=
  RealInducedPairSingleZero.filtration

end Langlands.Archimedean
