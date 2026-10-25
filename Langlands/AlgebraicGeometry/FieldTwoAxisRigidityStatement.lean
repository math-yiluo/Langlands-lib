import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Two-axis rigidity for smooth proper pointed products over fields -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A scheme morphism from a product of smooth proper geometrically connected
pointed schemes over any field, constant with the same value on both axes,
is constant. The target is separated and locally of finite type. -/
def FieldTwoAxisRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (Y Z P : Over (Spec (CommRingCat.of K))),
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom →
    IsSeparated P.hom → LocallyOfFiniteType P.hom →
    ∀ (y₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y)
      (z₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Z)
      (p₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P)
      (g : Y ⨯ Z ⟶ P),
      prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z) ≫ g =
        Over.mkIdTerminal.from Z ≫ p₀ →
      prod.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀) ≫ g =
        Over.mkIdTerminal.from Y ≫ p₀ →
      g = Over.mkIdTerminal.from (Y ⨯ Z) ≫ p₀

end Langlands.AlgebraicGeometry
