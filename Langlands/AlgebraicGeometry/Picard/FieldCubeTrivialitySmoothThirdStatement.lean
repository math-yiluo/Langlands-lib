import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement

/-! # The theorem of the cube over a field with a smooth, possibly non-proper third factor -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- A line bundle on `X ×_K (Y ×_K Z)` over any field `K` is trivial if it is
trivial on the three faces through the specified points, where `X` and `Y` are
smooth, proper and geometrically connected, and `Z` is smooth and geometrically
connected but not assumed proper. -/
def FieldCubeTrivialitySmoothThirdStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X Y Z : Over (Spec (CommRingCat.of K))),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    Smooth Z.hom → GeometricallyConnected Z.hom →
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
