import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Derived subgroups of commutative group schemes and perfect triviality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G D : GroupScheme S}

/-- A separated commutative group scheme has trivial scheme-theoretic derived subgroup. -/
theorem derivedSubgroup_eq_bot_of_isCommMonObj (G : GroupScheme S)
    [IsCommMonObj G.X] [IsSeparated G.X.hom] : derivedSubgroup G = ⊥ := by
  apply le_antisymm
  · rw [← range_kernelUnit G]
    apply derivedSubgroup_le_range _ (kernelUnit_isClosedSubgroup G)
    rw [range_kernelUnit]
    intro T x y
    change x * y * x⁻¹ * y⁻¹ = 1
    simp [mul_assoc]
  · intro T x hx
    have hx : x = 1 := hx
    rw [hx]
    exact Subgroup.one_mem _

/-- Every actual derived subgroup of a separated commutative group scheme is isomorphic
to the actual trivial group scheme over the same base. -/
def IsDerivedSubgroup.commSourceIsoTrivial {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    [IsCommMonObj G.X] [IsSeparated G.X.hom] : D ≅ Grp.trivial (Over S) :=
  hd.isRepresentedBy.isoOfIsRepresentedBy (by
    rw [derivedSubgroup_eq_bot_of_isCommMonObj G]
    exact bot_isRepresentedBy_kernelUnit G)

/-- A separated commutative group scheme whose full derived subgroup is the whole group
is isomorphic to the trivial group scheme. -/
def commutativePerfectIsoTrivial (G : GroupScheme S)
    [IsCommMonObj G.X] [IsSeparated G.X.hom]
    (hperfect : derivedSubgroup G = ⊤) : G ≅ Grp.trivial (Over S) :=
  (show IsDerivedSubgroup (𝟙 G) from
    ⟨(derivedSubgroup_total_admissible G).1,
      (SubgroupFunctor.range_id G).trans hperfect.symm⟩).commSourceIsoTrivial

end Langlands.GroupScheme
