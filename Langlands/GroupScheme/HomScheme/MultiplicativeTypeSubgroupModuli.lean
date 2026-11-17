import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation

/-! # Actual families of closed subgroups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

open TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- An actual subgroup functor represented by a closed group of multiplicative type. -/
def IsAdmissible (F : SubgroupFunctor G) : Prop :=
  ∃ (K : GroupScheme S) (j : K ⟶ G),
    IsClosedSubgroup j ∧ RelativeMultiplicativeType.IsMultiplicativeType K ∧
      F.IsRepresentedBy j

/-- A closed inclusion of a group of multiplicative type supplies an admissible subgroup. -/
theorem isAdmissible_range {K : GroupScheme S} (j : K ⟶ G)
    (hj : IsClosedSubgroup j) (hK : RelativeMultiplicativeType.IsMultiplicativeType K) :
    IsAdmissible (SubgroupFunctor.range j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨K, j, hj, hK, ⟨Over.mono_of_mono_left _, rfl⟩⟩

/-- Admissible actual subgroups remain admissible after arbitrary base change. -/
theorem IsAdmissible.baseChange {F : SubgroupFunctor G}
    (hF : IsAdmissible F) (b : S' ⟶ S) : IsAdmissible (F.baseChange b) := by
  obtain ⟨K, j, hj, hK, hF⟩ := hF
  exact ⟨(GroupScheme.baseChange b).obj K, (GroupScheme.baseChange b).map j,
    IsClosedSubgroup.baseChange b hj, hK.baseChange b, hF.baseChange b⟩

variable {M T : Over S} {K : GroupScheme M.left}

/-- Evaluation of a closed multiplicative-type family is an admissible actual subgroup. -/
theorem isAdmissible_evaluate
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeMultiplicativeType.IsMultiplicativeType K) (a : T ⟶ M) :
    IsAdmissible (evaluate j a) :=
  isAdmissible_range (familyHom j a) (isClosedSubgroup_familyHom j hj a)
    (hK.baseChange a.left)

/-- An actual family is universal when every closed multiplicative-type subgroup on
every base change is its evaluation at a unique actual parameter morphism. -/
def IsUniversal (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) : Prop :=
  ∀ (T : Over S) (F : SubgroupFunctor ((GroupScheme.baseChange T.hom).obj G)),
    IsAdmissible F → ∃! a : T ⟶ M, evaluate j a = F

end Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli
