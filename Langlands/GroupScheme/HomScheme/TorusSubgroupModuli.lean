import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Actual universal families of closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- A subgroup functor represented by an actual closed relative torus. -/
def IsAdmissible (F : SubgroupFunctor G) : Prop :=
  ∃ (K : GroupScheme S) (j : K ⟶ G),
    IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧ F.IsRepresentedBy j

/-- An actual closed torus inclusion supplies an admissible subgroup functor. -/
theorem isAdmissible_range {K : GroupScheme S} (j : K ⟶ G)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K) :
    IsAdmissible (SubgroupFunctor.range j) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨K, j, hj, hK, ⟨Over.mono_of_mono_left _, rfl⟩⟩

/-- Closed torus subgroup functors remain such after arbitrary base change. -/
theorem IsAdmissible.baseChange {F : SubgroupFunctor G}
    (hF : IsAdmissible F) (b : S' ⟶ S) : IsAdmissible (F.baseChange b) := by
  obtain ⟨K, j, hj, hK, hF⟩ := hF
  exact ⟨(GroupScheme.baseChange b).obj K, (GroupScheme.baseChange b).map j,
    IsClosedSubgroup.baseChange b hj, hK.baseChange b, hF.baseChange b⟩

variable {M T : Over S} {K : GroupScheme M.left}

/-- Pull an actual subgroup family to a test scheme, identifying the ambient
iterated pullback with its specified direct pullback to the original base. -/
def familyHom (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (a : T ⟶ M) :
    (GroupScheme.baseChange a.left).obj K ⟶ (GroupScheme.baseChange T.hom).obj G :=
  (GroupScheme.baseChange a.left).map j ≫
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).hom

/-- Evaluate a subgroup family by its actual range on every test scheme. -/
def evaluate (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (a : T ⟶ M) :
    SubgroupFunctor ((GroupScheme.baseChange T.hom).obj G) :=
  SubgroupFunctor.range (familyHom j a)

/-- Evaluation preserves closedness of the actual subgroup inclusion. -/
theorem isClosedSubgroup_familyHom
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (a : T ⟶ M) : IsClosedSubgroup (familyHom j a) := by
  let : IsClosedImmersion ((GroupScheme.baseChange a.left).map j).hom.hom.left :=
    IsClosedSubgroup.baseChange a.left hj
  change IsClosedImmersion
    (((GroupScheme.baseChange a.left).map j).hom.hom.left ≫
      (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).hom.hom.hom.left)
  infer_instance

/-- Every evaluation of a closed relative-torus family is admissible. -/
theorem isAdmissible_evaluate
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (a : T ⟶ M) : IsAdmissible (evaluate j a) :=
  isAdmissible_range (familyHom j a) (isClosedSubgroup_familyHom j hj a)
    (hK.baseChange a.left)

/-- A subgroup family is universal when every actual closed torus subgroup on
every base change is its evaluation at a unique actual parameter morphism. -/
def IsUniversal (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) : Prop :=
  ∀ (T : Over S) (F : SubgroupFunctor ((GroupScheme.baseChange T.hom).obj G)),
    IsAdmissible F → ∃! a : T ⟶ M, evaluate j a = F

end Langlands.GroupScheme.TorusSubgroupModuli
