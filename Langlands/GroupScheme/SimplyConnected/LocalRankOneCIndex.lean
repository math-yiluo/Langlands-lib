import Langlands.GroupScheme.SimplyConnected.LocalRankOneCMarkedVertex
import Langlands.GroupScheme.Quaternionic.LocalWittIndexOneDimension

/-! # The complete local rank-one type-C index alternative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- An actual local rank-one group of type C has precisely the rank-two or
rank-three index with vertex 2 marked and trivial full star action. -/
theorem localRankOneTypeC_index
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (hrank : splitRank G = 1) :
    d.HasRankOneCIndex n := by
  obtain ⟨hP, hmark, hstar⟩ :=
    localRankOneTypeC_presentation_and_marking d e hn hsc has hcartan hrank
  obtain ⟨P⟩ := hP
  have hbound := P.involution.card_le_three_of_wittIndex_one
    P.finrank_eq_four P.symmetric_finrank P.antihermitian P.unit P.wittIndex_eq_one
  simp only [Fintype.card_fin] at hbound
  exact ⟨by omega, ⟨e, hmark⟩, hstar⟩

/-- The actual group has a quaternionic symplectic model in either two or
three variables, with no characteristic restriction. -/
theorem nonempty_localRankOneTypeCSmallPresentation
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (hrank : splitRank G = 1) :
    Nonempty (LocalRankOneTypeCPresentation K G 2 ⊕
      LocalRankOneTypeCPresentation K G 3) := by
  obtain ⟨P⟩ :=
    (localRankOneTypeC_presentation_and_marking d e hn hsc has hcartan hrank).1
  have hsmall := (localRankOneTypeC_index d e hn hsc has hcartan hrank).1
  rcases hsmall with rfl | rfl
  · exact ⟨Sum.inl P⟩
  · exact ⟨Sum.inr P⟩

/-- Choose the actual rank-two or rank-three quaternionic symplectic
presentation of a local rank-one group with a type-C Cartan numbering. -/
def localRankOneTypeCSmallPresentation
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (hrank : splitRank G = 1) :
    LocalRankOneTypeCPresentation K G 2 ⊕ LocalRankOneTypeCPresentation K G 3 :=
  Classical.choice
    (nonempty_localRankOneTypeCSmallPresentation d e hn hsc has hcartan hrank)

end Langlands.GroupScheme
