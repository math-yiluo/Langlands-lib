import Langlands.Representation.Archimedean.RealInducedSwapUnlinked
import Langlands.Representation.Archimedean.RealInducedPairKTypeTransport
import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement
import Langlands.Representation.Archimedean.RealInducedPairLeftZero
import Langlands.Representation.Archimedean.RealInducedPairRightZero
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-! # The actual adjacent filtration away from positive linked indices -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration

namespace RealInducedPairUnlinkedFiltration

open RealInducedPairLinkedReplacement

/-- Compact-type counting makes the published nonzero-weight unlinked swap bijective. -/
theorem exists_bijective_intertwiner (d e : ComplexCharacterData)
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hord : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e)) :
    ∃ T : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 [.induced e, .induced d],
      IsRealIntertwinerModulo 4 [.induced d, .induced e] [.induced e, .induced d] ⊥ T ∧
        Function.Bijective T := by
  have hi : RealInjectiveIntertwinerExists 4 [.induced d, .induced e]
      [.induced e, .induced d] := by
    simpa using realInducedSwap 4 [] [] d e hd he rfl hord hun
  obtain ⟨T, hTi, hT⟩ := hi
  have hTm : IsRealIntertwinerModulo 4 [.induced d, .induced e]
      [.induced e, .induced d] ⊥ T :=
    InductionStages.isRealIntertwinerModulo_iff.mpr (by
      simpa only [Submodule.mem_bot, sub_eq_zero] using
        InductionStages.isRealStandardIntertwiner_iff.mp hT)
  exact ⟨T, hTm, hTi, RealInducedPairKTypeTransport.surjective_of_injective d e
    hTm.isRealKEquivariant hTi⟩

/-- A nonzero-weight unlinked ascending pair has a one-source filtration. -/
theorem filtration_of_unlinked (d e : ComplexCharacterData)
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e))
    (hun : AreRealBlocksUnlinked (.induced e) (.induced d)) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  obtain ⟨T, hT, hTb⟩ := exists_bijective_intertwiner e d he hd hlt.le hun
  refine (realAdjacentFiltration_iff 4 [] [] _ _).mpr ?_
  refine ((HasFiltration.self (n := 4)
    (P := fun es => es = [.induced e, .induced d]) rfl).map T hT hTb.2).mono ?_
  rintro es rfl
  exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩

/-- For an ascending nonzero-weight pair, absence of a linked index gives unlinked data. -/
theorem unlinked_of_no_linked (d e : ComplexCharacterData)
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e))
    (hn : ∀ k : ℕ, ¬ IsLinkedAt d e k) :
    AreRealBlocksUnlinked (.induced e) (.induced d) := by
  intro a ha b hb
  simp only [realBlockMoeglinData, hd, he, ite_false, List.mem_singleton] at ha hb
  subst a
  subst b
  rintro ⟨m, hm, hg | hg⟩
  · apply hn (m - 1)
    have hc : m = (m - 1) + 1 := by omega
    have hcf : (m : ℂ) = ((m - 1 : ℕ) : ℂ) + 1 := by exact_mod_cast hc
    have habs : ((e.weight.natAbs : ℤ) - d.weight.natAbs).natAbs =
        ((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs := by
      simpa only [neg_sub] using
        Int.natAbs_neg ((d.weight.natAbs : ℤ) - e.weight.natAbs)
    unfold IsLinkedAt
    rw [hcf, habs] at hg
    simpa only [add_assoc] using hg
  · have hr := congrArg Complex.re hg
    have hre : d.exponent.re - e.exponent.re =
        (((((e.weight.natAbs : ℤ) - d.weight.natAbs).natAbs : ℕ) : ℝ) / 2) +
          (m : ℝ) := by
      simpa using hr
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have ha : (0 : ℝ) ≤
        (((((e.weight.natAbs : ℤ) - d.weight.natAbs).natAbs : ℕ) : ℝ) / 2) :=
      by positivity
    change d.exponent.re < e.exponent.re at hlt
    linarith

/-- The complete ascending nonlinked branch, including original weights zero. -/
theorem filtration (d e : ComplexCharacterData)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e))
    (hn : ∀ k : ℕ, ¬ IsLinkedAt d e k) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  by_cases hd : d.weight = 0
  · exact RealInducedPairLeftZero.filtration 4 [] [] d e hd rfl hlt
  by_cases he : e.weight = 0
  · exact RealInducedPairRightZero.filtration 4 [] [] d e he rfl hlt
  exact filtration_of_unlinked d e hd he hlt (unlinked_of_no_linked d e hd he hlt hn)

end RealInducedPairUnlinkedFiltration

open RealInducedPairLinkedReplacement in
/-- Every ascending two-induction-block pair with no positive linked index has a filtration. -/
def RealInducedPairUnlinkedFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData,
    realBlockExponent (.induced d) < realBlockExponent (.induced e) →
    (∀ k : ℕ, ¬ IsLinkedAt d e k) →
      RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairUnlinkedFiltration : RealInducedPairUnlinkedFiltrationStatement :=
  RealInducedPairUnlinkedFiltration.filtration

end Langlands.Archimedean
