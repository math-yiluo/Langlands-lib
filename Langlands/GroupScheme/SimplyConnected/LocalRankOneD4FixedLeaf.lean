import Langlands.GroupScheme.SimplyConnected.TypeD4StarOrbits
import Langlands.GroupScheme.SimplyConnected.LocalRankOneDStar

/-! # Local rank-one type D4 from a globally fixed leaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A leaf fixed by the full star action supplies a quaternionic spin
presentation and exactly the central distinguished vertex in local type D4. -/
theorem localRankOneD4_presentation_and_marking_of_fixed_leaf
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1)
    (hfixed : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (hrank : splitRank G = 1) :
    Nonempty (LocalRankOneTypeDPresentation K G 4) ∧
      d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) (d.d4NumberingAt e a) :=
  localRankOneTypeD_presentation_and_marking d (d.d4NumberingAt e a)
    (by decide) hsc haas (d.d4NumberingAt_cartan e hD a ha)
    (d.star_fixes_nonfork_of_D4_fixed_leaf e hD a ha hfixed) hrank

/-- Choose the actual quaternionic spin presentation established using a
globally fixed leaf, without supplying fixation of a numbered long arm. -/
def localRankOneD4PresentationOfFixedLeaf
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1)
    (hfixed : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (hrank : splitRank G = 1) : LocalRankOneTypeDPresentation K G 4 :=
  Classical.choice
    (localRankOneD4_presentation_and_marking_of_fixed_leaf
      d e hsc haas hD a ha hfixed hrank).1

namespace TitsIndexData

/-- A nontrivial full star action with any globally fixed leaf gives the
exact published outer-D4 index after reorienting at that leaf. -/
theorem hasRankOneOuterD4Index_of_fixed_leaf
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1)
    (hfixed : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (hrank : splitRank G = 1) (hnot : ¬ d.StarIsTrivial) :
    d.HasRankOneOuterD4Index :=
  d.hasRankOneOuterD4Index_of_fixes_nonfork (d.d4NumberingAt e a) hsc haas
    (d.d4NumberingAt_cartan e hD a ha)
    (d.star_fixes_nonfork_of_D4_fixed_leaf e hD a ha hfixed) hrank hnot

/-- The remaining non-outer-D4 branch has no globally fixed leaf and its
distinguished set is either the center or all three leaves. -/
theorem localRankOneD4_index_or_transitive_leaf_marking
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hrank : splitRank G = 1) (hnot : ¬ d.StarIsTrivial) :
    d.HasRankOneOuterD4Index ∨
      ((¬ ∃ a : d.Vertex, e a ≠ 1 ∧
        ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) ∧
        ((∀ a, a ∈ d.distinguishedVertices ↔ e a = 1) ∨
          (∀ a, a ∈ d.distinguishedVertices ↔ e a ≠ 1))) := by
  classical
  by_cases hfixed : ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a
  · obtain ⟨a, ha, hfix⟩ := hfixed
    exact Or.inl (d.hasRankOneOuterD4Index_of_fixed_leaf
      e hsc haas hD a ha hfix hrank hnot)
  · exact Or.inr ⟨hfixed, d.D4_marking_cases_of_no_fixed_leaf e hD hrank hfixed⟩

end TitsIndexData

end Langlands.GroupScheme
