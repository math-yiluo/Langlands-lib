import Langlands.CategoryTheory.Renard.NoetherianCriteriaStatements
import Mathlib.Order.WellFounded

namespace Langlands.Renard

open CategoryTheory

universe u v

/-- The source maximal-subset predicate agrees with Mathlib Noetherianity. -/
theorem noetherianMathlibComparison (C : Type u) [Category.{v} C] :
    NoetherianMathlibComparisonStatement C := by
  intro X
  change IsNoetherianObject X ↔ (CategoryTheory.isNoetherianObject).Is X
  rw [CategoryTheory.ObjectProperty.is_iff]
  change IsNoetherianObject X ↔ WellFoundedGT (Subobject X)
  rw [WellFounded.wellFoundedGT_iff_exists_maximal]
  constructor
  · intro h S hS
    obtain ⟨P, hP, hmax⟩ := h S hS
    exact ⟨P, hP, fun Q hQ hPQ => (hmax Q hQ hPQ).le⟩
  · intro h S hS
    obtain ⟨P, hP, hmax⟩ := h S hS
    exact ⟨P, hP, fun Q hQ hPQ => le_antisymm (hmax hQ hPQ) hPQ⟩

/-- Source Noetherianity is uniform eventual stabilization of monotone sequences. -/
theorem noetherianSequenceStabilization (C : Type u) [Category.{v} C] :
    NoetherianSequenceStabilizationStatement C := by
  intro X
  rw [noetherianMathlibComparison C X,
    CategoryTheory.isNoetherianObject_iff_monotone_chain_condition X]
  constructor
  · intro h f hf
    exact h ⟨f, hf⟩
  · intro h f
    exact h f f.monotone

/-- Source Noetherianity is maximality in every nonempty subobject chain. -/
theorem noetherianChainMaximality (C : Type u) [Category.{v} C] :
    NoetherianChainMaximalityStatement C := by
  intro X
  constructor
  · intro h S hS _
    exact h S hS
  · intro h
    apply (noetherianSequenceStabilization C X).mpr
    intro f hf
    obtain ⟨P, ⟨n, rfl⟩, hmax⟩ :=
      h (Set.range f) (Set.range_nonempty f) hf.isChain_range
    exact ⟨n, fun m hnm => (hmax (f m) (Set.mem_range_self m) (hf hnm)).symm⟩

/-- Renard A.I.3: the three exact Noetherian-object criteria. -/
theorem noetherianCriteria (C : Type u) [Category.{v} C] :
    NoetherianCriteriaStatement C :=
  ⟨noetherianMathlibComparison C, noetherianChainMaximality C,
    noetherianSequenceStabilization C⟩

end Langlands.Renard
