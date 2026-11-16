import Langlands.GroupScheme.SimplyConnected.TypeD4CentralMarking
import Langlands.GroupScheme.SimplyConnected.LocalRankOneD4FixedLeaf

/-! # Exact central marking for every local rank-one type-D4 index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Every local simply connected absolutely almost-simple index of split rank
one and actual type D4 has exactly its central vertex distinguished. -/
theorem localRankOneD4_central_marking
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hrank : splitRank G = 1) :
    d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e := by
  classical
  by_cases hfixed : ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a
  · obtain ⟨a, ha, hfix⟩ := hfixed
    have hmarked := (localRankOneD4_presentation_and_marking_of_fixed_leaf
      d e hsc haas hD a ha hfix hrank).2.2
    refine ⟨hD, fun b => (hmarked b).trans ?_⟩
    have hc : Equiv.swap (e a) 0 (1 : Fin 4) = 1 := by
      exact Equiv.swap_apply_of_ne_of_ne ha.symm (by decide)
    have heq : d.d4NumberingAt e a b = 1 ↔ e b = 1 := by
      change Equiv.swap (e a) 0 (e b) = 1 ↔ e b = 1
      constructor
      · intro h
        exact (Equiv.swap (e a) 0).injective (h.trans hc.symm)
      · intro h
        rw [h, hc]
    simpa [Fin.ext_iff] using heq
  · exact d.D4_central_marking_of_no_fixed_leaf e hD hrank hfixed

end Langlands.GroupScheme.TitsIndexData
