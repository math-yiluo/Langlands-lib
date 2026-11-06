import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper maps of algebraic spaces over local fields are proper on rational points

Conrad's Corollary 5.6: over a local field `K`, possibly archimedean, a proper map between
quasi-separated algebraic spaces locally of finite type induces a topologically proper map on
rational points.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Corollary 5.6 (printed p.16): let `K` be a local field, that is, a nontrivially
normed field that is locally compact. For a proper map `f : X ⟶ Y` between quasi-separated
algebraic spaces locally of finite type over `Spec K`, the induced map `X(K) → Y(K)` is a
proper map for the étale-chart topologies. -/
def LocalFieldProperPointMapStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K]
    (X Y : AlgebraicSpace (Spec (CommRingCat.of K))) (f : X ⟶ Y),
    IsQuasiSeparated X → LocallyOfFiniteTypeOverBase X →
    IsQuasiSeparated Y → LocallyOfFiniteTypeOverBase Y →
    IsProperMorphism f →
      @IsProperMap _ _ (etaleChartTopology K X) (etaleChartTopology K Y)
        (RingPoints.map (A := K) f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
