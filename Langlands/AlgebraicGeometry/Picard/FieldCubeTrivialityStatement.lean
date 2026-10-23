import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # The geometric theorem of the cube over an arbitrary field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace CubeFace

variable {S : Scheme.{u}} (X Y Z : Over S)

/-- Insert the specified section in the first coordinate. -/
def first (x₀ : Over.mk (𝟙 S) ⟶ X) : Y ⨯ Z ⟶ X ⨯ (Y ⨯ Z) :=
  prod.lift (Over.mkIdTerminal.from (Y ⨯ Z) ≫ x₀) (𝟙 (Y ⨯ Z))

/-- Insert the specified section in the second coordinate. -/
def second (y₀ : Over.mk (𝟙 S) ⟶ Y) : X ⨯ Z ⟶ X ⨯ (Y ⨯ Z) :=
  prod.lift prod.fst
    (prod.lift (Over.mkIdTerminal.from (X ⨯ Z) ≫ y₀) prod.snd)

/-- Insert the specified section in the third coordinate. -/
def third (z₀ : Over.mk (𝟙 S) ⟶ Z) : X ⨯ Y ⟶ X ⨯ (Y ⨯ Z) :=
  prod.lift prod.fst
    (prod.lift prod.snd (Over.mkIdTerminal.from (X ⨯ Y) ≫ z₀))

end CubeFace

/-- A line bundle on a product of three smooth proper geometrically connected
pointed schemes over any field is trivial if it is trivial on the three faces
through the specified points. -/
def FieldCubeTrivialityStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X Y Z : Over (Spec (CommRingCat.of K))),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom →
    ∀ (x₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
      (y₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y)
      (z₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Z)
      (L : LineBundle (X ⨯ (Y ⨯ Z)).left),
      Nonempty ((Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
        Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj L.obj ≅
        Langlands.Scheme.Modules.structureSheaf (X ⨯ Z).left) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj L.obj ≅
        Langlands.Scheme.Modules.structureSheaf (X ⨯ Y).left) →
      Nonempty (L.obj ≅ Langlands.Scheme.Modules.structureSheaf (X ⨯ (Y ⨯ Z)).left)

end Langlands.AlgebraicGeometry.Picard
