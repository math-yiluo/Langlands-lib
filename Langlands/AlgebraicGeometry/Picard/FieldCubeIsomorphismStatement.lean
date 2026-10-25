import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement

/-! # The two-line-bundle isomorphism form of the geometric theorem of the cube -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Two line bundles on a product of three smooth proper geometrically connected
pointed schemes over any field are isomorphic if their restrictions to the three
faces through the specified points are isomorphic. -/
def FieldCubeIsomorphismStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X Y Z : Over (Spec (CommRingCat.of K))),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom →
    ∀ (x₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
      (y₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Y)
      (z₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Z)
      (L M : LineBundle (X ⨯ (Y ⨯ Z)).left),
      Nonempty ((Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
        (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj M.obj) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj L.obj ≅
        (Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj M.obj) →
      Nonempty ((Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj L.obj ≅
        (Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj M.obj) →
      Nonempty (L.obj ≅ M.obj)

end Langlands.AlgebraicGeometry.Picard
