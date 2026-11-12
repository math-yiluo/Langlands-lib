import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Mathlib.Analysis.Normed.Field.Basic

/-! # Smooth algebraic-space maps on points over complete normed fields -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A smooth morphism of separated algebraic spaces locally of finite type over a complete
nontrivially normed field induces an open map on rational points with the étale-chart
topologies. No representability, surjectivity or fibre-connectedness hypothesis is needed. -/
def CompleteFieldSmoothSpacePointOpenStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (X Y : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSeparated X → LocallyOfFiniteTypeOverBase X →
    IsSeparated Y → LocallyOfFiniteTypeOverBase Y →
    ∀ f : X ⟶ Y, IsSmoothMorphism f →
      @IsOpenMap (RingPoints K X K) (RingPoints K Y K)
        (etaleChartTopology K X) (etaleChartTopology K Y) (RingPoints.map f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
