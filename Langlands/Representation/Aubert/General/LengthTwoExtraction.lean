import Langlands.Representation.Aubert.General.LengthTwoExtractionStatement
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.Data.ENat.SuccOrder

/-! # Actual two-factor extraction from a composition-length bound -/

noncomputable section

namespace Langlands.SmoothRep

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero reducible smooth representation has a nonzero proper invariant
subspace. No finite-length hypothesis is needed. -/
theorem exists_proper_subrepresentation_of_not_irreducible
    (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A]
    (hred : ¬ A.IsIrreducible) :
    ∃ S : Subrepresentation A.representation, S ≠ ⊥ ∧ S ≠ ⊤ := by
  classical
  have hbt : (⊥ : Subrepresentation A.representation) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    apply hv
    have hmem : v ∈ (⊥ : Subrepresentation A.representation) := by
      rw [h]
      exact Submodule.mem_top
    exact hmem
  by_contra h
  apply hred
  refine
    { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
      eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · exact Or.inr (by by_contra hS'; exact h ⟨S, hS, hS'⟩)

/-- The canonical subrepresentation inclusion and quotient projection form an
actual short exact sequence of smooth representations. -/
theorem subrepresentation_quotient_shortExact
    (A : SmoothRep.{uK, uG, uV} k G) (S : Subrepresentation A.representation) :
    IsShortExact (hom (subtype A S)) (hom (mkQ A S)) := by
  refine ⟨subtype_injective A S, mkQ_surjective A S, ?_⟩
  change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

/-- If an actual smooth representation has length at most two, every nonzero
proper invariant subspace and its actual quotient have length one. -/
theorem subrepresentation_quotient_length_eq_one
    (A : SmoothRep.{uK, uG, uV} k G)
    (hA : repLength A.representation ≤ 2)
    (S : Subrepresentation A.representation) (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    repLength (subrepresentation A S).representation = 1 ∧
      repLength (quotient A S).representation = 1 := by
  have hS0' : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS0 (Subrepresentation.toSubmodule_injective h)
  have hS1' : S.toSubmodule ≠ ⊤ := by
    intro h
    exact hS1 (Subrepresentation.toSubmodule_injective h)
  have hsub : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS0'
  have hquot : Nontrivial (A ⧸ S.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hS1'
  have hsubpos : 0 < repLength (subrepresentation A S).representation :=
    repLength_pos_iff.mpr hsub
  have hquotpos : 0 < repLength (quotient A S).representation :=
    repLength_pos_iff.mpr hquot
  have hsubone : 1 ≤ repLength (subrepresentation A S).representation :=
    Order.one_le_iff_pos.mpr hsubpos
  have hquotone : 1 ≤ repLength (quotient A S).representation :=
    Order.one_le_iff_pos.mpr hquotpos
  have hsum : repLength (subrepresentation A S).representation +
      repLength (quotient A S).representation ≤ 2 := by
    have hs := subrepresentation_quotient_shortExact A S
    rw [repLength_eq_add_of_exact (hom (subtype A S)) (hom (mkQ A S))
      hs.1 hs.2.1 hs.2.2] at hA
    exact hA
  constructor
  · apply le_antisymm _ hsubone
    apply (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    exact (add_le_add le_rfl hquotone).trans hsum
  · apply le_antisymm _ hquotone
    apply (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    exact (add_le_add hsubone le_rfl).trans hsum

/-- A nonzero reducible smooth representation with composition length at most
two has two actual finite-length irreducible factors in a short exact sequence.
Finite length of the original representation is not a hypothesis. -/
theorem exists_two_irreducible_factors_of_length_le_two
    (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A]
    (hA : repLength A.representation ≤ 2) (hred : ¬ A.IsIrreducible) :
    ∃ B C : FiniteLengthObject.{uK, uG, uV} k G,
      B.val.IsIrreducible ∧ C.val.IsIrreducible ∧
      ∃ (f : B.val.representation.IntertwiningMap A.representation)
        (g : A.representation.IntertwiningMap C.val.representation), IsShortExact f g := by
  obtain ⟨S, hS0, hS1⟩ := exists_proper_subrepresentation_of_not_irreducible A hred
  obtain ⟨hB, hC⟩ := subrepresentation_quotient_length_eq_one A hA S hS0 hS1
  have hBfl : (subrepresentation A S).HasFiniteLength := by
    apply Module.length_ne_top_iff.mp
    change repLength (subrepresentation A S).representation ≠ ⊤
    rw [hB]
    simp
  have hCfl : (quotient A S).HasFiniteLength := by
    apply Module.length_ne_top_iff.mp
    change repLength (quotient A S).representation ≠ ⊤
    rw [hC]
    simp
  exact ⟨⟨subrepresentation A S, hBfl⟩, ⟨quotient A S, hCfl⟩,
    repLength_eq_one_iff.mp hB, repLength_eq_one_iff.mp hC,
    hom (subtype A S), hom (mkQ A S), subrepresentation_quotient_shortExact A S⟩

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Algebraic extraction of the actual factor conclusion in the general
rank-one target from a nonzero reducible object and its length bound. -/
theorem exists_hasTwoConstituents_of_length_le_two
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : repLength A.representation ≤ 2) (hred : ¬ A.IsIrreducible) :
    ∃ ρplus ρminus : SmoothRep.FiniteLengthObject.{0, uG, uV} ℂ G,
      HasTwoConstituents A ρplus.val ρminus.val := by
  obtain ⟨B, C, hB, hC, f, g, hfg⟩ :=
    SmoothRep.exists_two_irreducible_factors_of_length_le_two A hA hred
  exact ⟨B, C, hB, hC, Or.inl ⟨f, g, hfg⟩⟩

/-- The same extraction directly from a supplied bounded composition series,
as produced by the finite exact-family length criterion. -/
theorem exists_hasTwoConstituents_of_compositionLengthAtMost_two
    (A : SmoothRep.{0, uG, uV} ℂ G) [Nontrivial A]
    (hA : HasCompositionLengthAtMost A.obj 2) (hred : ¬ A.IsIrreducible) :
    ∃ ρplus ρminus : SmoothRep.FiniteLengthObject.{0, uG, uV} ℂ G,
      HasTwoConstituents A ρplus.val ρminus.val := by
  obtain ⟨n, hn, s, hs⟩ := hA
  apply exists_hasTwoConstituents_of_length_le_two A ?_ hred
  change repLength A.obj.ρ ≤ 2
  rw [repLength_eq_of_hasSimpleFactors s hs]
  exact_mod_cast hn

/-- The closed algebraic extraction prerequisite with independent group and
carrier universes. -/
theorem twoConstituentExtraction : TwoConstituentExtractionStatement.{uG, uV} := by
  intro G _ _ A _ hA hred
  exact exists_hasTwoConstituents_of_length_le_two A hA hred

end Langlands.Aubert.General
