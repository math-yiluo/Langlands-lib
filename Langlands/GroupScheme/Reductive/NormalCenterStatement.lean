import Langlands.GroupScheme.Derived.CenterReduction

/-! # Full centres of normal connected reductive subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The full centre of a closed normal connected reductive subgroup maps
into the ambient full centre. This is a structural proposition target. -/
def NormalReductiveCenterStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (i : H ⟶ G), IsClosedSubgroup i →
      (SubgroupFunctor.range i).IsNormal →
      center H ≤ (center G).comap i

/-- Conditional on full-centre containment, the source centre is exactly
the inverse image of the ambient full centre. -/
theorem center_eq_comap_of_normalReductiveCenterStatement
    (hcenter : NormalReductiveCenterStatement.{u})
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hnormal : (SubgroupFunctor.range i).IsNormal) :
    center H = (center G).comap i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact le_antisymm (hcenter k G H hG hH i hi hnormal)
    (center_comap_le_of_mono i)

end Langlands.GroupScheme
