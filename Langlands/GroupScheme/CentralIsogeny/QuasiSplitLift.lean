import Langlands.GroupScheme.CentralIsogeny.QuasiSplitLiftStatement
import Langlands.GroupScheme.CentralIsogeny.BorelPreimage
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Quasi-splitness lifts along central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Quasi-splitness lifts along central isogenies.** The scheme-theoretic preimage of a
geometric Borel subgroup of `A` under a central isogeny `π : G ⟶ A` is a geometric Borel
subgroup of `G`: after base change to an algebraic closure it is the preimage of a Borel
subgroup, which is Borel by `CentralIsogenyBorelPreimage.isBorelSubgroup_of_range_eq_comap`. -/
theorem centralIsogenyQuasiSplitLift : CentralIsogenyQuasiSplitLiftStatement.{u} := by
  intro K _ G A π hπ hG hA
  have := hG.isAffineHom
  obtain ⟨B, j, hj⟩ := hA.exists_isGeometricBorelSubgroup
  have hjc : IsClosedSubgroup j := hj.1.isClosedSubgroup
  let i := SubgroupPreimage.inclusion π j
  have hi : IsClosedSubgroup i := SubgroupPreimage.isClosedSubgroup π j hjc
  refine ⟨hG, SubgroupPreimage.groupScheme π j, i,
    isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure ?_ hi⟩
  let b := toAlgebraicClosure K
  let F := GroupScheme.baseChange b
  exact CentralIsogenyBorelPreimage.isBorelSubgroup_of_range_eq_comap
    hG.baseChange_toAlgebraicClosure hA.isConnectedReductive.baseChange_toAlgebraicClosure
    (F.map π) (hπ.baseChange b) (F.map j) hj.2 (F.map i) (hi.baseChange b) (by
      rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
        SubgroupPreimage.range_inclusion, SubgroupFunctor.comap_baseChange])

end Langlands.GroupScheme
