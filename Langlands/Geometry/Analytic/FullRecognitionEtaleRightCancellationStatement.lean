import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition

/-! # Strong étale right cancellation over all affinoid pieces -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- If the second map and the composite are étale over all recognized
affinoid pieces, then the first map is étale over all recognized pieces.
Quasifiniteness of the first map is part of the conclusion, not a premise. -/
def EtaleRightCancellationStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom B.saturatedPresentation C.saturatedPresentation),
    g'.IsEtaleAllPieces →
      (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces →
      g.IsEtaleAllPieces

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
