import Langlands.GroupScheme.Reductive.GeneralLinearGeometricStatement
import Langlands.GroupScheme.Reductive.GeneralLinearProof
import Langlands.GroupScheme.Reductive.GeometricReductivityProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Geometric reductivity of `GL_n` and the radicals of its block parabolics: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

/-- `GL_n` is geometrically reductive over every algebraically closed field, and over every
field its block unipotent subgroup is the geometric unipotent radical of its block parabolic. -/
theorem geometricStructureStatement : GeometricStructureStatement.{u} :=
  ⟨fun k _ _ n _ _ =>
      isGeometricallyReductive_of_statement reductiveGeometricReductivity
        (reductiveStatement.1 k n).isPseudoReductive,
    fun k _ n _ _ e =>
      dynamicGeometricUnipotentRadical k _ (reductiveStatement.1 k n) _ _ _ _ _
        (isRepresentedBy_parabolic_diagonalCocharacter n _ e)
        (by
          rw [Category.assoc, blockUnipotentIsoKernel_hom_comp]
          exact isRepresentedBy_unipotent_diagonalCocharacter n _ e)⟩

end Langlands.GroupScheme.GeneralLinear
