import Langlands.Representation.Archimedean.RealInducedPairSingleZero
import Langlands.Representation.Archimedean.RealInducedSwapArithmetic
import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement

/-!
# The nonlinked arithmetic region with one zero induction weight

The mixed Mœglin conditions reduce to the same positive gap as those for two
nonzero induction weights. The proved single-zero exchange then supplies the
filtration whenever no positive linked index exists.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement

namespace RealInducedPairUnlinkedRegion

/-- The same two arithmetic obstructions describe unlinkedness whenever
at least one induction weight is nonzero. -/
theorem unlinked_iff {d e : ComplexCharacterData}
    (hnz : d.weight ≠ 0 ∨ e.weight ≠ 0) :
    AreRealBlocksUnlinked (.induced d) (.induced e) ↔
      ∀ k : ℕ, 0 < k →
        d.exponent - e.exponent ≠
            ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) ∧
          e.exponent - d.exponent ≠
            ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) := by
  by_cases hd : d.weight = 0
  · have he : e.weight ≠ 0 := hnz.resolve_left (not_not.mpr hd)
    simp [AreRealBlocksUnlinked, realBlockMoeglinData, hd, he, MoeglinDatum.IsLinked,
      not_exists, not_and, not_or]
    simp only [and_comm]
  · by_cases he : e.weight = 0
    · simp [AreRealBlocksUnlinked, realBlockMoeglinData, hd, he, MoeglinDatum.IsLinked,
        not_exists, not_and, not_or]
    · exact RealInducedSwapArithmetic.unlinked_iff hd he

/-- For descending blocks, the reverse difference cannot be a linking value. -/
theorem unlinked_iff_of_order {d e : ComplexCharacterData}
    (hnz : d.weight ≠ 0 ∨ e.weight ≠ 0)
    (horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d)) :
    AreRealBlocksUnlinked (.induced d) (.induced e) ↔
      ∀ k : ℕ, 0 < k →
        d.exponent - e.exponent ≠
          ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) := by
  rw [unlinked_iff hnz]
  constructor
  · exact fun h k hk => (h k hk).1
  · intro h k hk
    exact ⟨h k hk, RealInducedSwapArithmetic.reverse_difference_ne horder hk⟩

/-- Descending unlinkedness is exactly the absence of a positive linked index
for the ascending pair, when at least one weight is nonzero. -/
theorem unlinked_reverse_iff_no_linked {d e : ComplexCharacterData}
    (hnz : d.weight ≠ 0 ∨ e.weight ≠ 0)
    (horder : realBlockExponent (.induced d) ≤ realBlockExponent (.induced e)) :
    AreRealBlocksUnlinked (.induced e) (.induced d) ↔
      ∀ k : ℕ, ¬ IsLinkedAt d e k := by
  have habs : ((e.weight.natAbs : ℤ) - d.weight.natAbs).natAbs =
      ((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs := by
    have hs : (e.weight.natAbs : ℤ) - d.weight.natAbs =
        -((d.weight.natAbs : ℤ) - e.weight.natAbs) := by omega
    rw [hs, Int.natAbs_neg]
  rw [unlinked_iff_of_order hnz.symm horder, habs]
  constructor
  · intro h k hk
    apply h (k + 1) (by omega)
    simpa only [IsLinkedAt, Nat.cast_add, Nat.cast_one, add_assoc] using hk
  · intro h k hk heq
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    apply h j
    simpa only [IsLinkedAt, Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_assoc] using heq

/-- Exactly one zero weight and no positive linked index give the actual
ascending adjacent filtration. -/
theorem filtration_of_no_linked (d e : ComplexCharacterData)
    (hz : (d.weight = 0 ∧ e.weight ≠ 0) ∨ (d.weight ≠ 0 ∧ e.weight = 0))
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e))
    (hnl : ∀ k : ℕ, ¬ IsLinkedAt d e k) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hnz : d.weight ≠ 0 ∨ e.weight ≠ 0 := by
    rcases hz with ⟨_, he⟩ | ⟨hd, _⟩
    · exact Or.inr he
    · exact Or.inl hd
  exact RealInducedPairSingleZero.filtration d e hz hlt
    ((unlinked_reverse_iff_no_linked hnz hlt.le).mpr hnl)

end RealInducedPairUnlinkedRegion

/-- The adjacent filtration for exactly one zero induction weight in the
region with no positive linked index. -/
def RealInducedPairSingleZeroNonlinkedFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData,
    ((d.weight = 0 ∧ e.weight ≠ 0) ∨ (d.weight ≠ 0 ∧ e.weight = 0)) →
      realBlockExponent (.induced d) < realBlockExponent (.induced e) →
        (∀ k : ℕ, ¬ IsLinkedAt d e k) →
          RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairSingleZeroNonlinkedFiltration :
    RealInducedPairSingleZeroNonlinkedFiltrationStatement :=
  RealInducedPairUnlinkedRegion.filtration_of_no_linked

end Langlands.Archimedean
