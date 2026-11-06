import Langlands.Representation.Finite.BrauerLatticeProof
import Langlands.Representation.Finite.VirtualCharacterProof

/-!
# Finite complex Brauer theory

A proof of `Langlands.FiniteRep.FiniteBrauerTheoryStatement`. Integral Brauer spanning in the
representation group follows from the character-lattice equality and faithfulness of character
realization; the remaining conjuncts are the proved component theorems.
-/

noncomputable section

namespace Langlands.FiniteRep.BrauerTheory

universe uG

section Spanning

variable {G : Type uG} [Group G] [Fintype G]

/-- Character realization of a Brauer expansion is the same integral combination of the
induced rank-one characters. -/
theorem virtualCharacter_brauerExpansion (c : MonomialDatum ℂ G →₀ ℤ) :
    virtualCharacter (k := ℂ) (G := G) (brauerExpansion G c) =
      Finsupp.linearCombination ℤ (inducedCharacter (k := ℂ) (G := G)) c := by
  have h : (⇑(virtualCharacter (k := ℂ) (G := G)) ∘ fun d : MonomialDatum ℂ G =>
      ofClass (induce d.1 (classOf (oneDimensional d.2)))) = inducedCharacter := by
    funext d
    simp only [Function.comp_apply, virtualCharacter_ofClass, inducedCharacter]
  rw [brauerExpansion, Finsupp.apply_linearCombination, h]

/-- Every virtual representation is a signed integral sum of rank-one subgroup inductions. -/
theorem spanning : IntegralBrauerSpanningStatement G := by
  intro x
  have hL : inducedCharacterLattice (k := ℂ) (G := G) = virtualCharacters (k := ℂ) (G := G) :=
    BrauerLattice.characterLattice
  have hx : virtualCharacter (k := ℂ) (G := G) x ∈ inducedCharacterLattice (k := ℂ) (G := G) := by
    rw [hL]
    exact ⟨x, rfl⟩
  rw [inducedCharacterLattice, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, VirtualCharacter.faithfulness ?_⟩
  rw [virtualCharacter_brauerExpansion, Finsupp.linearCombination_apply]
  exact hc

end Spanning

/-- The finite complex Brauer and character-realization prerequisites. -/
theorem finiteBrauerTheory (G : Type uG) [Group G] [Fintype G] : FiniteBrauerTheoryStatement G :=
  ⟨InducedCharacter.rankOneOrder G, InducedCharacter.inducedCharacterFormula,
    InducedCharacter.inducedDegree G, VirtualCharacter.faithfulness,
    VirtualCharacter.irreducibleBasis, spanning, BrauerLattice.characterLattice⟩

end Langlands.FiniteRep.BrauerTheory
