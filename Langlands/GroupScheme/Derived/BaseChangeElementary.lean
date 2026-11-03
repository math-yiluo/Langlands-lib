import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Elementary base-change lemmas for the derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H D : GroupScheme S}

namespace SubgroupFunctor

/-- An all-test commutator containment remains true after any base change. -/
theorem ContainsCommutators.baseChange {F : SubgroupFunctor G}
    (hF : F.ContainsCommutators) : (F.baseChange b).ContainsCommutators := by
  intro T x y
  change baseChangePointsEquiv b G T (x * y * x⁻¹ * y⁻¹) ∈
    F.carrier ((Over.map b).obj T)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hF _ _ _

end SubgroupFunctor

/-- The derived subgroup after base change is contained in the base change of
its defining intersection. No representability premise is needed. -/
theorem derivedSubgroup_baseChange_le :
    derivedSubgroup ((GroupScheme.baseChange b).obj G) ≤ (derivedSubgroup G).baseChange b := by
  intro T x hx
  change baseChangePointsEquiv b G T x ∈
    (derivedSubgroup G).carrier ((Over.map b).obj T)
  intro H i hi hcomm
  have hiComm : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).ContainsCommutators := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hcomm.baseChange b
  have h := derivedSubgroup_le_range ((GroupScheme.baseChange b).map i)
    (hi.baseChange b) hiComm T hx
  rw [SubgroupFunctor.range_baseChangeHom] at h
  exact h

/-- Equality of the full derived subgroup functors carries every exhibiting
closed inclusion to an exhibiting inclusion after base change. -/
theorem IsDerivedSubgroup.baseChange_of_eq {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (heq : (derivedSubgroup G).baseChange b =
      derivedSubgroup ((GroupScheme.baseChange b).obj G)) :
    IsDerivedSubgroup ((GroupScheme.baseChange b).map d) := by
  refine ⟨hd.1.baseChange b, ?_⟩
  rw [SubgroupFunctor.range_baseChangeHom, hd.2, heq]

end Langlands.GroupScheme
