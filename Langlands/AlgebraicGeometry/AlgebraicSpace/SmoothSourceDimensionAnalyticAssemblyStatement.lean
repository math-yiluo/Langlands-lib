import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticAtlas

/-! # Analytic assembly across actual smooth dimension pieces -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

/-- The actual varying-dimensional atlas assembled from an analytic pure-dimensional
family has analytic transitions on the original rational-point space. This
derived bridge uses henselianity for the open embeddings of the actual pieces;
completeness, map functoriality and local analytic inverses are separate. -/
def SmoothSourceDimensionAnalyticAssemblyStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsHenselianValuedField K)
    (σ : AnalyticPointStructure K), σ.IsAnalytic →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X)
      (hqs : IsQuasiSeparated X) (hls : IsLocallySeparated X),
      (σ.dimensionAtlas hK hX hqs hls).IsAnalytic

end Langlands.AlgebraicGeometry.AlgebraicSpace
