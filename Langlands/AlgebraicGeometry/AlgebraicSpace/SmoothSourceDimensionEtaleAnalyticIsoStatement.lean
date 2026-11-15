import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticAtlas

/-! # Étale local analytic isomorphisms across actual dimension pieces -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

/-- An actual étale morphism preserves intrinsic point dimension and induces
analytic local inverse branches for the assembled varying-dimensional atlases
of an admissible pure-dimensional family. -/
def SmoothSourceDimensionEtaleAnalyticIsoStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsHenselianValuedField K)
    (σ : AnalyticPointStructure K), σ.IsAdmissible →
    ∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
      (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
      (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
      (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (f : X ⟶ Y),
      IsEtaleMorphism f →
      (σ.dimensionAtlas hK hX hXqs hXls).IsLocalAnalyticIso
        (σ.dimensionAtlas hK hY hYqs hYls) (RingPoints.map (A := K) f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
