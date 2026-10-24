import Langlands.AbelianScheme.BalancedCubeFaces

/-! # Transporting an identity-fibre trivialization to the cube faces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.GroupScheme.BalancedCube

variable {S : Scheme.{u}} (G : Grp (Over S))

/-- The actual pullback of the line bundle along the identity section. -/
abbrev identityFibre (L : LineBundle G.X.left) : S.Modules :=
  pull G L (1 : Over.mk (𝟙 S) ⟶ G.X)

/-- A supplied trivialization at the identity induces a trivialization of the
constant identity pullback on every domain over the base. -/
def constantIdentityIso (L : LineBundle G.X.left) (T : Over S)
    (e : identityFibre G L ≅ structureSheaf S) :
    pull G L (1 : T ⟶ G.X) ≅ structureSheaf T.left := by
  let q : T ⟶ Over.mk (𝟙 S) := Over.mkIdTerminal.from T
  simpa only [MonObj.comp_one, structureSheaf] using
    (pullPullIso G L q (1 : Over.mk (𝟙 S) ⟶ G.X)).symm ≪≫
      (Scheme.Modules.pullback q.left).mapIso e ≪≫ pullbackUnitIso q.left

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (L : LineBundle G.X.left)
variable (e : identityFibre G L ≅ structureSheaf S)

/-- The first face comparison obtained from the supplied identity fibre. -/
def firstFaceIsoOfIdentityFibre :
    (Scheme.Modules.pullback (firstFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (firstFace G).left).obj (cubeNegative G L) :=
  firstFaceIso G preservation L (constantIdentityIso G L (G.X ⨯ G.X) e)

/-- The second face comparison obtained from the supplied identity fibre. -/
def secondFaceIsoOfIdentityFibre :
    (Scheme.Modules.pullback (secondFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (secondFace G).left).obj (cubeNegative G L) :=
  secondFaceIso G preservation L (constantIdentityIso G L (G.X ⨯ G.X) e)

/-- The third face comparison obtained from the supplied identity fibre. -/
def thirdFaceIsoOfIdentityFibre :
    (Scheme.Modules.pullback (thirdFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (thirdFace G).left).obj (cubeNegative G L) :=
  thirdFaceIso G preservation L (constantIdentityIso G L (G.X ⨯ G.X) e)

end Langlands.GroupScheme.BalancedCube
