import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms

/-! # Descent of finite étaleness along a finite étale surjection -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- Let `q` be finite étale from an open set `E` onto an open Hausdorff set `V`,
and let the composite of `q` and `f` be finite étale from `E` to an open set
`T`. Then `f` is finite étale from `V` to `T`. The field, space and index
universes are independent. -/
def FiniteEtaleOverSourceDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B C : AffinoidAtlasPresentation.{u, v, w} K)
    (q : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (f : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (E : Set A.space) (V : Set B.space) (T : Set C.space),
    IsOpen E → IsOpen V → IsOpen T → T2Space V →
    q.baseMap '' E = V →
    q.IsFiniteEtaleOver E V →
    (q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteEtaleOver E T →
    f.IsFiniteEtaleOver V T

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
