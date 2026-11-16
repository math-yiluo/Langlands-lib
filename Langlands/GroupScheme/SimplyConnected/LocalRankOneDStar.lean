import Langlands.GroupScheme.SimplyConnected.TypeDRankOneOrbit
import Langlands.GroupScheme.SimplyConnected.LocalRankOneDMarkedVertex

/-! # Local rank-one type D without a supplied nonfork star condition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- For every local rank-one group with an actual type-D numbering of rank
at least five, the quaternionic spin model and exact marked vertex require
no supplied condition on the full star action. -/
theorem localRankOneTypeD_presentation_and_marking_of_five_le
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 5 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hrank : splitRank G = 1) :
    Nonempty (LocalRankOneTypeDPresentation K G n) ∧
      d.IsNumberingOf (CartanMatrix.D n) (fun i => i.val = 1) e :=
  localRankOneTypeD_presentation_and_marking d e (by omega) hsc haas hD
    (d.star_fixes_nonfork_of_D hn e hD) hrank

/-- Choose the proved quaternionic spin presentation for an actual type-D
numbering of rank at least five, without a supplied star-action premise. -/
def localRankOneTypeDPresentationOfFiveLe
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 5 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hrank : splitRank G = 1) : LocalRankOneTypeDPresentation K G n :=
  Classical.choice
    (localRankOneTypeD_presentation_and_marking_of_five_le d e hn hsc haas hD hrank).1

namespace TitsIndexData

/-- An inner local rank-one D5 group has precisely the published inner-D5
index, with the original actual numbering. -/
theorem hasRankOneInnerD5Index_of_type_D_five
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 5)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 5 (e a) (e b))
    (hrank : splitRank G = 1) (hstar : d.StarIsTrivial) :
    d.HasRankOneInnerD5Index :=
  ⟨⟨e, (localRankOneTypeD_presentation_and_marking_of_five_le
    d e (by decide) hsc haas hD hrank).2⟩, hstar⟩

/-- In rank four, fixed nonfork vertices and a nontrivial full star action
give exactly the published outer-D4 index. -/
theorem hasRankOneOuterD4Index_of_fixes_nonfork
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hfix : ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < 4 → d.star σ a = a)
    (hrank : splitRank G = 1) (hnot : ¬ d.StarIsTrivial) :
    d.HasRankOneOuterD4Index := by
  refine ⟨e, (localRankOneTypeD_presentation_and_marking
    d e (by decide) hsc haas hD hfix hrank).2, ?_⟩
  exact d.starImagePair_of_D_of_fixes_nonfork (by decide) e hD hfix hnot

end TitsIndexData

end Langlands.GroupScheme
