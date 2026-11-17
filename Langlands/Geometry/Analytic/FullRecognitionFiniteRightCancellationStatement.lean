import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods

/-! # Finite right cancellation over a common open base -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- Two finite maps over the same open base make the intervening actual
strong map finite. Recognition of all its affinoid preimages is part of the
conclusion. -/
def FiniteOverRightCancellationStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : Set A.space) (U : Set B.space) (T : Set C.space),
    IsOpen V → IsOpen U → IsOpen T → g.baseMap '' V ⊆ U →
      g'.IsFiniteOver U T →
      (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V T →
      g.IsFiniteOver V U

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
