import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticAtlas

/-! # Analytic functoriality across actual smooth dimension pieces -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

/-- Every morphism between actual smooth spaces is analytic for the assembled
varying-dimensional atlases of an admissible pure-dimensional family. All
source and target chart intersections occur in the conclusion. -/
def SmoothSourceDimensionAnalyticFunctorialityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsHenselianValuedField K)
    (σ : AnalyticPointStructure K), σ.IsAdmissible →
    ∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
      (hX : SmoothOverBase X) (hY : SmoothOverBase Y)
      (hXqs : IsQuasiSeparated X) (hXls : IsLocallySeparated X)
      (hYqs : IsQuasiSeparated Y) (hYls : IsLocallySeparated Y) (f : X ⟶ Y),
      (σ.dimensionAtlas hK hX hXqs hXls).AnalyticMap
        (σ.dimensionAtlas hK hY hYqs hYls) (RingPoints.map (A := K) f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
