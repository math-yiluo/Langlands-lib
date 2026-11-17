import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms

/-! # Finiteness from affinoid target neighborhoods -/

universe u v w

open scoped Topology

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- The target-local criterion for a finite morphism between open subsets:
finite actual pullbacks on a finite affinoid neighborhood family at every
target point imply recognized finite pullbacks over every target affinoid. -/
def FiniteOverTargetLocalityStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space),
    IsOpen V → IsOpen U → g.baseMap '' V ⊆ U →
      (∀ x ∈ U, ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset,
        I.Finite ∧
        (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ U ∧
          ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
            (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
            P.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
              (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach) ∧
        (⋃ W ∈ I, W.locus) ∈ 𝓝 x) →
      g.IsFiniteOver V U

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
