import Langlands.GroupScheme.Reductive.TitsIndexRelativeStatement
import Langlands.GroupScheme.Reductive.TitsIndexStarProof
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasisProof
import Langlands.GroupScheme.Rational.RelativeRankIdentityProof
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Split rank of an actual Tits index

The distinguished star orbits and the actual simple relative roots of a
Tits-index datum both count the split rank of the semisimple group. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A semisimple field group has no nonzero rational characters: it equals its
derived subgroup, on which every character restricts to zero. -/
theorem IsSemisimple.subsingleton_rationalCharacters
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) :
    Subsingleton (rationalCharacters G) := by
  have hderived : IsDerivedSubgroup (𝟙 G) := by
    refine ⟨IsClosedSubgroup.of_iso (Iso.refl G), ?_⟩
    rw [semisimplePerfect k G hG]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
    exact SubgroupFunctor.mem_range.2 ⟨x, by simp⟩
  constructor
  intro χ ψ
  have hχ := hderived.characterRestrict_eq_zero χ
  have hψ := hderived.characterRestrict_eq_zero ψ
  rw [characterRestrict_id] at hχ hψ
  exact hχ.trans hψ.symm

/-- The rational-character rank of a semisimple field group is zero. -/
theorem IsSemisimple.rationalCharacterRank_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) :
    rationalCharacterRank G = 0 := by
  have := hG.subsingleton_rationalCharacters
  rw [rationalCharacterRank]
  exact Module.finrank_zero_of_subsingleton

namespace TitsIndexData

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The actual simple relative roots of the maximal split torus and generic
cocharacter carried by a Tits-index datum are finite in number, and their number,
cast to `ℕ∞`, is the split rank of the semisimple group. -/
theorem card_simpleRelativeRoots_eq_splitRank (d : TitsIndexData G) :
    (Nat.card (simpleRelativeRoots d.splitInclusion d.positiveCocharacter) : ℕ∞) =
      splitRank G := by
  have hG : IsConnectedReductive G := d.isSemisimple.isConnectedReductive
  obtain ⟨-, -, hbasis⟩ := relativeSimpleRootBasis k G hG d.splitTorus d.splitInclusion
    d.maximalSplit d.positiveCocharacter d.generic
  obtain ⟨-, -, -, hsplit, hsum, -⟩ :=
    relativeRankIdentity k G hG d.splitTorus d.splitInclusion d.maximalSplit
  rw [hsplit, hsum, d.isSemisimple.rationalCharacterRank_eq_zero, add_zero, hbasis]

end TitsIndexData

/-- Reduction of the split-rank target to the relative simple-root comparison:
the orbit-to-root equivalence identifies the two cardinalities, and the actual
simple relative roots count the split rank of a semisimple group. -/
theorem titsIndexSplitRankStatement_of_relativeSimpleRoots
    (h : TitsIndexRelativeSimpleRootsStatement.{u}) :
    TitsIndexSplitRankStatement.{u} := by
  intro k _ G _ _ d
  obtain ⟨-, e, -⟩ := h k G d
  have hroots := d.card_simpleRelativeRoots_eq_splitRank
  exact ⟨by rw [Nat.card_congr e, hroots], hroots⟩

/-- The finite number of distinguished star orbits and the number of actual
simple relative roots of a Tits-index datum compute the `ℕ∞` split rank. -/
theorem titsIndexSplitRank : TitsIndexSplitRankStatement.{u} :=
  titsIndexSplitRankStatement_of_relativeSimpleRoots titsIndexRelativeSimpleRoots

/-- The complete relative-structure interface of the actual Tits index. -/
theorem titsIndexRelativeStructure : TitsIndexRelativeStructureStatement.{u} :=
  ⟨titsIndexStarRelativeRoots, titsIndexSplitRank⟩

end Langlands.GroupScheme
