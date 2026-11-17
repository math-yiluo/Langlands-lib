import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition

/-! # Pointwise étaleness from a finite neighborhood family to every recognized piece -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- A finite neighborhood family of recognized affinoid pieces on which the
induced finite maps are étale at the given point supplies the same pointwise
condition over every recognized target piece, after choosing finite open
neighborhoods as in `HasAllPiecesAt`. -/
def FinitePiecesEtaleAllPiecesStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space),
    g.HasFinitePiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y →
      g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
