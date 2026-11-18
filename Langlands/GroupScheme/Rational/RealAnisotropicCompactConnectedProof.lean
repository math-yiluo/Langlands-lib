import Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedStatement
import Langlands.GroupScheme.Rational.RealAnisotropicTorusBound
import Langlands.GroupScheme.Rational.RealPolarCompactness
import Langlands.GroupScheme.Rational.RealCompactPointsConnected
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.SmoothAffinePointLieGroup
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Real points of anisotropic connected reductive groups are compact and connected -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold

set_option linter.defProp false in
/-- **Real points of anisotropic reductive groups** (Borel–Tits 1965, 9.4 and 14.3): the real
points of an anisotropic connected reductive group over `ℝ` form a compact connected space.
This is a proved definition: its type is the proposition `RealAnisotropicCompactConnectedStatement`. -/
def realAnisotropicCompactConnected : RealAnisotropicCompactConnectedStatement := by
  intro G _ hG hA
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)
  have : CompactSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    RealPolar.compactSpace_of_torusBound G hG
      fun _ ρ _ _ hT hi => hA.exists_abs_rationalMatrix_le_of_closedTorus ρ hT hi
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left _ G.X.hom hG.smooth hG.connectedSpace
  let := realSmoothAffineChartedSpace G.X n hn
  have : LocallyConnectedSpace (RingPoint ℝ G.X ℝ) :=
    ChartedSpace.locallyConnectedSpace (Fin n → ℝ) _
  let e := G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ)
  have : LocallyConnectedSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    e.isOpenEmbedding.locallyConnectedSpace
  have hconn := RealCompactPoints.connectedSpace_of_compactSpace G hG
  exact ⟨e.compactSpace, e.surjective.connectedSpace e.continuous⟩

end Langlands.GroupScheme
