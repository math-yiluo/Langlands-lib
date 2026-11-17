import Langlands.GroupScheme.Derived.GeneralLinearCenter
import Langlands.GroupScheme.Derived.GeneralLinearDerived
import Langlands.GroupScheme.Derived.GeneralLinearQuotientPerfect

/-! # Centre and derived group of GL, and perfectness of its central quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The centre of GL consists of unit scalar matrices, its derived group is SL, and
all its fppf quotients by the centre are perfect, in every rank and over every field. -/
theorem generalLinearCenterDerived : GeneralLinearCenterDerivedStatement.{u} := by
  intro k _ n
  refine ⟨GeneralLinear.mem_center_iff_scalar (Fin n) (CommRingCat.of k),
    SpecialLinear.isDerivedSubgroup_inclusion (Fin n) k, ?_⟩
  intro Q q hq
  apply GeneralLinear.quotient_derivedSubgroup_eq_top (Fin n) k q ?_ hq
  intro T g hg
  rw [← (SpecialLinear.isDerivedSubgroup_inclusion (Fin n) k).2]
  exact (SpecialLinear.mem_range_inclusion_iff (Fin n) (CommRingCat.of k) T g).mpr hg

end Langlands.GroupScheme
