import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceStatement
import Langlands.GroupScheme.Dynamic.UnipotentStructure
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Unipotence of dynamic unipotent subgroups from two general unipotence inputs -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Unipotence of the standard upper unitriangular groups and inheritance of
unipotence by closed subgroups imply that every representative of `U_G(χ)` is
unipotent. -/
def DynamicUnipotentUnipotenceReductionStatement : Prop :=
  UnitriangularUnipotentStatement.{u} → UnipotentClosedSubgroupStatement.{u} →
    DynamicUnipotentUnipotenceStatement.{u}

/-- The chosen closed representative of `U_G(χ)` is unipotent by
`Dynamic.isUnipotent_of_unitriangular_inputs`; every other representative is
isomorphic to it. -/
theorem dynamicUnipotentUnipotenceReduction :
    DynamicUnipotentUnipotenceReductionStatement.{u} := by
  intro htri hclosed k _ G _ _ χ H j hj
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact IsUnipotent.of_iso
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hj
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ))
    (Dynamic.isUnipotent_of_unitriangular_inputs χ (Dynamic.Affine.unipotentHom χ)
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom χ) htri hclosed)

end Langlands.GroupScheme
