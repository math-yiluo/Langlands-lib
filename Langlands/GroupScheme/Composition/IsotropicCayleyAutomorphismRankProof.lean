import Langlands.GroupScheme.Composition.IsotropicCayleyAutomorphismRankStatement
import Langlands.GroupScheme.Composition.CayleyGradingTorus
import Langlands.GroupScheme.Composition.CayleyPeirceFrame
import Langlands.GroupScheme.Composition.CayleyPeirceExistence

/-! # Split rank two for isotropic Cayley automorphism group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CayleyDatum

variable {K : Type u} [Field K] {c : CayleyDatum K}

/-- An automorphism group scheme of a Cayley datum admitting a Peirce frame has split
rank two. -/
theorem splitRank_eq_two_of_peirceFrame {H : GroupScheme (Spec (CommRingCat.of K))}
    {iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)}
    (hrep : c.IsAutomorphismRepresentation iH) (D : c.PeirceFrame) : splitRank H = 2 := by
  refine le_antisymm (splitRank_le_two hrep) ?_
  obtain ⟨g, hgen⟩ : ∃ g : c.Grading (ULift.{u} (Fin 2) → ℤ),
      AddSubgroup.closure (g.support : Set (ULift.{u} (Fin 2) → ℤ)) = ⊤ := D.exists_grading
  have h := g.card_le_splitRank hrep hgen
  simpa [Nat.card_eq_fintype_card] using h

end CayleyDatum

/-- Over every field, a group scheme realizing the full automorphism functor of a Cayley
datum with isotropic norm has split rank two. -/
theorem isotropicCayleyAutomorphismRank : IsotropicCayleyAutomorphismRankStatement.{u} := by
  intro K _ c H iH hrep ⟨x, hx, hN⟩
  obtain ⟨e, he, hte⟩ := c.exists_norm_eq_zero_trace_eq_one hx hN
  obtain ⟨u, v, hu, hv, huv⟩ := c.exists_peirceFrame he hte
  exact CayleyDatum.splitRank_eq_two_of_peirceFrame hrep ⟨e, u, v, he, hte, hu, hv, huv⟩

end Langlands.GroupScheme
