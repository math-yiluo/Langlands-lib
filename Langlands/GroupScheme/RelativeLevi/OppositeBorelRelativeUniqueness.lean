import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.RelativeLevi.OppositeBorelFieldUniqueness
import Langlands.GroupScheme.RelativeLevi.ParabolicFibreEquality

/-! # Uniqueness of an opposite relative Borel through a maximal torus

The global comparison takes `RelativeParabolicLieContainmentStatement` as
an explicit hypothesis. The fibre comparison uses only published field results.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B B₁ B₂ : GroupScheme S}
  {T : CommGroupScheme S} (t : T.toGrp ⟶ G)
  (i : B ⟶ G) (i₁ : B₁ ⟶ G) (i₂ : B₂ ⟶ G)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Opposite relative Borels through a fibrewise maximal torus have equal
image subgroup functors on every residue-field fibre. -/
theorem oppositeRelativeBorel_residueFiber_range_eq
    (hG : IsReductive G) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hi₁ : IsRelativeBorelSubgroup i₁) (hi₂ : IsRelativeBorelSubgroup i₂)
    (h₁ : SubgroupFunctor.range i₁ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t)
    (h₂ : SubgroupFunctor.range i₂ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t)
    (s : S) :
    SubgroupFunctor.range (RelativeLevi.residueFiberHom i₁ s) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i₂ s) := by
  let b : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
  have hinter : ∀ {C : GroupScheme S} (j : C ⟶ G),
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t →
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j) ⊓
          SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
        SubgroupFunctor.range ((GroupScheme.baseChange b).map t) := by
    intro C j hj
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
      ← SubgroupFunctor.inf_baseChange, hj, SubgroupFunctor.range_baseChangeHom]
  exact oppositeGeometricBorel_range_eq
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.isConnectedReductive_residueFiber s)
    ((GroupScheme.baseChange b).map t) (hmax s)
    ((GroupScheme.baseChange b).map i) (hi.residueFiber s)
    ((GroupScheme.baseChange b).map i₁) (hi₁.residueFiber s)
    ((GroupScheme.baseChange b).map i₂) (hi₂.residueFiber s)
    (hinter i₁ h₁) (hinter i₂ h₂)

/-- Conditional on Lie containment spreading, two relative Borel subgroups
opposite to the same Borel through the same maximal torus are equal as
subgroup functors on all test schemes. -/
theorem oppositeRelativeBorel_range_eq
    (hLie : RelativeParabolicLieContainmentStatement.{u})
    (hG : IsReductive G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hi₁ : IsRelativeBorelSubgroup i₁) (hi₂ : IsRelativeBorelSubgroup i₂)
    (h₁ : SubgroupFunctor.range i₁ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t)
    (h₂ : SubgroupFunctor.range i₂ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t) :
    SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂ := by
  have ht₁ : SubgroupFunctor.range t ≤ SubgroupFunctor.range i₁ := by
    rw [← h₁]
    exact fun _ _ hx => hx.1
  have ht₂ : SubgroupFunctor.range t ≤ SubgroupFunctor.range i₂ := by
    rw [← h₂]
    exact fun _ _ hx => hx.1
  exact relativeParabolic_range_eq_of_residueFiber_range_eq i₁ i₂ T t hLie hG
    hi₁.isRelativeParabolicSubgroup hi₂.isRelativeParabolicSubgroup hT ht hmax ht₁ ht₂
    (oppositeRelativeBorel_residueFiber_range_eq t i i₁ i₂ hG hmax hi hi₁ hi₂ h₁ h₂)

end Langlands.GroupScheme
