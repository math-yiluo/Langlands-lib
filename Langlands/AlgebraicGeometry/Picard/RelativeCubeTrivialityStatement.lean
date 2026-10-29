import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement
import Langlands.AbelianScheme.Basic

/-! # The ordinary relative three-face cube criterion for abelian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Over any quasi-separated base, a line bundle on the product of three abelian schemes is
trivial if it is trivial on the three full faces through the unit sections. -/
def RelativeCubeTrivialityStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A B C : AbelianScheme S)
    (D : LineBundle (A.X ⨯ (B.X ⨯ C.X)).left),
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.first A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ A.X)).left).obj D.obj ≅
        structureSheaf (B.X ⨯ C.X).left) →
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.second A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ B.X)).left).obj D.obj ≅
        structureSheaf (A.X ⨯ C.X).left) →
    Nonempty ((Scheme.Modules.pullback
      (CubeFace.third A.X B.X C.X (1 : Over.mk (𝟙 S) ⟶ C.X)).left).obj D.obj ≅
        structureSheaf (A.X ⨯ B.X).left) →
    Nonempty (D.obj ≅ structureSheaf (A.X ⨯ (B.X ⨯ C.X)).left)

end Langlands.AbelianScheme
