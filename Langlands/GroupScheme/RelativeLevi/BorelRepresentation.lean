import Langlands.GroupScheme.RelativeLevi.BorelParameter
import Langlands.GroupScheme.RelativeLevi.BorelFamilyCriterion

/-! # An actual universal Borel family from a universal parabolic family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

open TorusSubgroupModuli

/-- An actual smooth proper parameter scheme with its universal relative Borel
family, classified by equality of subgroup functors on every test scheme. -/
structure BorelSchemeData {S : Scheme.{u}} (G : GroupScheme S) where
  parameter : Over S
  group : GroupScheme parameter.left
  inclusion : group ⟶ (baseChange parameter.hom).obj G
  isBorel : IsRelativeBorelSubgroup inclusion
  universal :
    ∀ (T : Over S) (B : GroupScheme T.left)
      (i : B ⟶ (baseChange T.hom).obj G), IsRelativeBorelSubgroup i →
        ∃! a : T ⟶ parameter, evaluate inclusion a = SubgroupFunctor.range i
  smooth : Smooth parameter.hom
  proper : IsProper parameter.hom

variable {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}
variable {P : GroupScheme M.left}

/-- Restrict an actual smooth proper universal parabolic family to its clopen
Borel locus, retaining the scheme, the pullback family and unique classification. -/
def borelSchemeDataOfParabolic
    (hcl : RelativeBorelLocusClopenStatement.{u}) (hG : IsReductive G)
    (j : P ⟶ (baseChange M.hom).obj G) (hj : IsRelativeParabolicSubgroup j)
    (hu : ∀ (T : Over S) (Q : GroupScheme T.left)
      (i : Q ⟶ (baseChange T.hom).obj G), IsRelativeParabolicSubgroup i →
        ∃! a : T ⟶ M, evaluate j a = SubgroupFunctor.range i)
    [Smooth M.hom] [IsProper M.hom] : BorelSchemeData G := by
  let U := borelParameterOpens hcl hG j hj
  let a : openParameter U ⟶ M := openParameterMap U
  refine ⟨openParameter U, (baseChange a.left).obj P, familyHom j a,
    ?_, ?_, smooth_openParameter U, isProper_borelParameter hcl hG j hj⟩
  · apply (isRelativeBorelSubgroup_familyHom_iff j hG hj a).mpr
    change Set.range U.ι ⊆ (U : Set M.left)
    rw [Scheme.Opens.range_ι]
  · intro T B i hi
    apply existsUnique_evaluate_openParameter j U (SubgroupFunctor.range i)
      (hu T B i hi.isRelativeParabolicSubgroup)
    intro b hb
    exact range_subset_borelLocus_of_evaluate_eq j hG hj b hi hb

end Langlands.GroupScheme.RelativeLevi
