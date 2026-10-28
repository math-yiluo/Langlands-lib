import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AbelianScheme.BalancedCubeIdentityFibre
import Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismStatement
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Balanced cube assembly from a supplied geometric comparison theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

namespace Langlands.GroupScheme

open BalancedCube

/-- An actual comparison of the balanced tensors on the triple product,
constructed from a supplied two-bundle geometric cube theorem. -/
def fieldComparisonCubeIso
    (cubeIso : FieldCubeIsomorphismStatement.{u})
    (K : Type u) [Field K] (G : Grp (Over (Spec (CommRingCat.of K))))
    (hs : Smooth G.X.hom) (hp : IsProper G.X.hom)
    (hc : GeometricallyConnected G.X.hom) (L : LineBundle G.X.left) :
    cubePositive G L ≅ cubeNegative G L := by
  let preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    pullbackTensorComparisonIsIso.{u}
  let origin : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := 1
  let e := Classical.choice (fieldLineBundleTriviality K
    ((LineBundle.pullback origin.left).obj L))
  let P := positiveLineBundle G preservation L
    (firstProjection G) (secondProjection G) (thirdProjection G)
  let N := negativeLineBundle G preservation L
    (firstProjection G) (secondProjection G) (thirdProjection G)
  exact Classical.choice (cubeIso K G.X G.X G.X
    hs hp hc hs hp hc hs hp hc origin origin origin P N
    ⟨firstFaceIsoOfIdentityFibre G preservation L e⟩
    ⟨secondFaceIsoOfIdentityFibre G preservation L e⟩
    ⟨thirdFaceIsoOfIdentityFibre G preservation L e⟩)

/-- Conditional final assembly. The two-bundle geometric cube theorem remains
an explicit premise; field triviality and tensor preservation are discharged. -/
theorem fieldCubePullbackOfIsomorphism
    (cubeIso : FieldCubeIsomorphismStatement.{u}) :
    FieldCubePullbackStatement.{u} := by
  intro K _ G _ hs hp hc T f g h L
  exact ⟨pullCubeIso G pullbackTensorComparisonIsIso.{u} L f g h
    (fieldComparisonCubeIso cubeIso K G hs hp hc L)⟩

end Langlands.GroupScheme
