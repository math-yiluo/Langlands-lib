import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily
import Langlands.GroupScheme.RelativeLevi.ParabolicSmoothMatching
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Actual parabolic families on supplied homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open SubgroupFunctor TorusSubgroupModuli

variable {S : Scheme.{u}} {G P : GroupScheme S} {M T : Over S}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)

include hG hi in
/-- An actual conjugate family of a relative parabolic is relative parabolic. -/
theorem isRelativeParabolicSubgroup_conjugateFamily (g : M ⟶ G.X) :
    IsRelativeParabolicSubgroup (conjugateFamily i g) :=
  (hi.baseChange hG M.hom).comp_iso
    (((GroupScheme.baseChange M.hom).obj G).innerIso
      ((baseChangeBasePointsEquiv M.hom G).symm g))

/-- The actual parabolic subgroup functor conjugated by a group-valued parameter. -/
def conjugateParabolic (g : M ⟶ G.X) :
    ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj G) :=
  ⟨range (conjugateFamily i g),
    isParabolic_range _ (isRelativeParabolicSubgroup_conjugateFamily hG i hi g)⟩

/-- Restriction of a conjugate family composes its actual group-valued parameter. -/
theorem restrict_conjugateParabolic (g : M ⟶ G.X) (a : T ⟶ M) :
    restrict hG a (conjugateParabolic hG i hi g) =
      conjugateParabolic hG i hi (a ≫ g) := by
  apply Subtype.ext
  rw [restrict_eq_evaluate hG _ (conjugateFamily i g) rfl a,
    evaluate_conjugateFamily]
  rfl

/-- Normalizer fibers give ordinary matching of the universal conjugate family. -/
theorem isMatchingAlong_conjugateParabolic {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ q = h ≫ q →
      g⁻¹ * h ∈ (range i).normalizer.carrier U) :
    IsMatchingAlong hG q (conjugateParabolic hG i hi (𝟙 G.X)) := by
  intro U g h hgh
  rw [restrict_conjugateParabolic, restrict_conjugateParabolic,
    Category.comp_id, Category.comp_id]
  apply Subtype.ext
  exact range_conjugateFamily_eq_of_normalizer i g h (hfib U g h hgh)

section Quotient

variable {Q : Over S} (q : G.X ⟶ Q) [Smooth q.left] [Surjective q.left]
    (hfib : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ q = h ≫ q →
      g⁻¹ * h ∈ (range i).normalizer.carrier U)

/-- Descend the universal conjugate family to a supplied smooth quotient
whose all-test fibers lie in full-normalizer cosets. -/
def quotientParabolic : ParabolicSubgroup ((GroupScheme.baseChange Q.hom).obj G) :=
  matchingSmooth hG q (conjugateParabolic hG i hi (𝟙 G.X))
    (isMatchingAlong_conjugateParabolic hG i hi q hfib)

/-- The descended quotient family pulls back to the universal conjugate family. -/
@[simp]
theorem restrict_quotientParabolic :
    restrict hG q (quotientParabolic hG i hi q hfib) =
      conjugateParabolic hG i hi (𝟙 G.X) :=
  restrict_matchingSmooth hG q _ _

/-- Every actual lift to the group evaluates the quotient family to the
parabolic conjugated by that lift, on arbitrary test schemes. -/
theorem restrict_quotientParabolic_comp (g : T ⟶ G.X) :
    restrict hG (g ≫ q) (quotientParabolic hG i hi q hfib) =
      conjugateParabolic hG i hi g := by
  rw [← restrict_comp, restrict_quotientParabolic, restrict_conjugateParabolic,
    Category.comp_id]

end Quotient

/-- The right-coset quotient of a parabolic supplies a quotient family even
without a self-normalizer premise, since every subgroup normalizes itself. -/
def homogeneousQuotientParabolic
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i) :
    ParabolicSubgroup ((GroupScheme.baseChange Q.scheme.hom).obj G) := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact quotientParabolic hG i hi Q.projection (fun U g h hgh =>
    (range i).le_normalizer U ((Q.fibers U g h).mp hgh))

end Langlands.GroupScheme.ParabolicSubgroupModuli
