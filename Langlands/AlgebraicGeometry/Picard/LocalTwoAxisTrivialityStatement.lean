import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Local triviality detected by two section axes and one fibre -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- A line bundle on the product of two smooth proper geometrically connected
families, trivial on both section axes and on a fibre, is trivial over a
neighbourhood of that base point. -/
def LocalTwoAxisTrivialityStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : Over S),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth Y.hom → IsProper Y.hom → GeometricallyConnected Y.hom →
    ∀ (x₀ : Over.mk (𝟙 S) ⟶ X) (y₀ : Over.mk (𝟙 S) ⟶ Y)
      (L : LineBundle (X ⨯ Y).left) (s : S),
      Nonempty ((Scheme.Modules.pullback
        (prod.lift (𝟙 X) (Over.mkIdTerminal.from X ≫ y₀)).left).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf X.left) →
      Nonempty ((Scheme.Modules.pullback
        (prod.lift (Over.mkIdTerminal.from Y ≫ x₀) (𝟙 Y)).left).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf Y.left) →
      Nonempty ((Scheme.Modules.pullback ((X ⨯ Y).hom.fiberι s)).obj L.obj ≅
        Langlands.Scheme.Modules.structureSheaf ((X ⨯ Y).hom.fiber s)) →
      ∃ U : S.Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback
          (pullback.fst (X ⨯ Y).hom U.ι)).obj L.obj ≅
            Langlands.Scheme.Modules.structureSheaf (pullback (X ⨯ Y).hom U.ι))

end Langlands.AlgebraicGeometry.Picard
