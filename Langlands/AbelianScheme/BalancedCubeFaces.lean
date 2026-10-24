import Langlands.AbelianScheme.BalancedCubeFactors
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement

/-! # Coordinate faces of the balanced cube tensors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.GroupScheme.BalancedCube

variable {S : Scheme.{u}} (G : Grp (Over S))

/-- The right-associated triple product used by the geometric cube statement. -/
abbrev cube : Over S := G.X ⨯ (G.X ⨯ G.X)

/-- The first coordinate of the triple product. -/
abbrev firstProjection : cube G ⟶ G.X := prod.fst

/-- The second coordinate of the triple product. -/
abbrev secondProjection : cube G ⟶ G.X := prod.snd ≫ prod.fst

/-- The third coordinate of the triple product. -/
abbrev thirdProjection : cube G ⟶ G.X := prod.snd ≫ prod.snd

/-- The actual positive tensor on the triple product. -/
abbrev cubePositive (L : LineBundle G.X.left) : (cube G).left.Modules :=
  positive G L (firstProjection G) (secondProjection G) (thirdProjection G)

/-- The actual pair tensor on the triple product. -/
abbrev cubeNegative (L : LineBundle G.X.left) : (cube G).left.Modules :=
  negative G L (firstProjection G) (secondProjection G) (thirdProjection G)

/-- The first cube face through the identity section. -/
abbrev firstFace : G.X ⨯ G.X ⟶ cube G :=
  CubeFace.first G.X G.X G.X (1 : Over.mk (𝟙 S) ⟶ G.X)

/-- The second cube face through the identity section. -/
abbrev secondFace : G.X ⨯ G.X ⟶ cube G :=
  CubeFace.second G.X G.X G.X (1 : Over.mk (𝟙 S) ⟶ G.X)

/-- The third cube face through the identity section. -/
abbrev thirdFace : G.X ⨯ G.X ⟶ cube G :=
  CubeFace.third G.X G.X G.X (1 : Over.mk (𝟙 S) ⟶ G.X)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (L : LineBundle G.X.left)

/-- The first face comparison, conditional only on tensor preservation and
a trivialization of the constant factor on its domain. -/
def firstFaceIso
    (e : pull G L (1 : G.X ⨯ G.X ⟶ G.X) ≅ structureSheaf (G.X ⨯ G.X).left) :
    (Scheme.Modules.pullback (firstFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (firstFace G).left).obj (cubeNegative G L) := by
  refine pullPositiveIso G preservation L (firstFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G) ≪≫ ?_ ≪≫
    (pullNegativeIso G preservation L (firstFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G)).symm
  simpa [firstFace, CubeFace.first, firstProjection, secondProjection, thirdProjection]
    using firstUnitIso G L (prod.fst : G.X ⨯ G.X ⟶ G.X) prod.snd e

/-- The second face comparison with the same explicit inputs. -/
def secondFaceIso
    (e : pull G L (1 : G.X ⨯ G.X ⟶ G.X) ≅ structureSheaf (G.X ⨯ G.X).left) :
    (Scheme.Modules.pullback (secondFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (secondFace G).left).obj (cubeNegative G L) := by
  refine pullPositiveIso G preservation L (secondFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G) ≪≫ ?_ ≪≫
    (pullNegativeIso G preservation L (secondFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G)).symm
  simpa [secondFace, CubeFace.second, firstProjection, secondProjection, thirdProjection]
    using secondUnitIso G L (prod.fst : G.X ⨯ G.X ⟶ G.X) prod.snd e

/-- The third face comparison with the same explicit inputs. -/
def thirdFaceIso
    (e : pull G L (1 : G.X ⨯ G.X ⟶ G.X) ≅ structureSheaf (G.X ⨯ G.X).left) :
    (Scheme.Modules.pullback (thirdFace G).left).obj (cubePositive G L) ≅
      (Scheme.Modules.pullback (thirdFace G).left).obj (cubeNegative G L) := by
  refine pullPositiveIso G preservation L (thirdFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G) ≪≫ ?_ ≪≫
    (pullNegativeIso G preservation L (thirdFace G)
      (firstProjection G) (secondProjection G) (thirdProjection G)).symm
  simpa [thirdFace, CubeFace.third, firstProjection, secondProjection, thirdProjection]
    using thirdUnitIso G L (prod.fst : G.X ⨯ G.X ⟶ G.X) prod.snd e

variable {T : Over S}

/-- The map from an arbitrary domain to the right-associated triple product. -/
def tripleMap (f g h : T ⟶ G.X) : T ⟶ cube G :=
  prod.lift f (prod.lift g h)

/-- Pulling an actual cube comparison back along three arbitrary maps gives the
balanced comparison, with no geometric condition on the domain. -/
def pullCubeIso (f g h : T ⟶ G.X)
    (e : cubePositive G L ≅ cubeNegative G L) :
    positive G L f g h ≅ negative G L f g h := by
  have ep :
      (Scheme.Modules.pullback (tripleMap G f g h).left).obj (cubePositive G L) ≅
        positive G L f g h := by
    simpa [tripleMap, firstProjection, secondProjection, thirdProjection] using
      pullPositiveIso G preservation L (tripleMap G f g h)
        (firstProjection G) (secondProjection G) (thirdProjection G)
  have en :
      (Scheme.Modules.pullback (tripleMap G f g h).left).obj (cubeNegative G L) ≅
        negative G L f g h := by
    simpa [tripleMap, firstProjection, secondProjection, thirdProjection] using
      pullNegativeIso G preservation L (tripleMap G f g h)
        (firstProjection G) (secondProjection G) (thirdProjection G)
  exact ep.symm ≪≫ (Scheme.Modules.pullback (tripleMap G f g h).left).mapIso e ≪≫ en

end Langlands.GroupScheme.BalancedCube
