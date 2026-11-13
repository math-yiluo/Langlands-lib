import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Mathlib.GroupTheory.PGroup

/-! # Point groups of unipotent groups in prime characteristic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
  {U G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]

/-- The actual points of an affine finite type unipotent group on every scheme
test form a `p`-group in prime characteristic `p`. -/
theorem isPGroup_testPoints_of_isUnipotent (hU : IsUnipotent U)
    (T : Over (Spec (CommRingCat.of k))) : IsPGroup p (T ⟶ U.X) := by
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hU
  exact isPGroup_iff_pow_pow_eq_one.mpr (fun x => ⟨r, hr T x⟩)

/-- The image of a unipotent group's test points under any group-scheme
homomorphism is a `p`-group. -/
theorem isPGroup_range_testPoints_of_isUnipotent (hU : IsUnipotent U)
    (i : U ⟶ G) (T : Over (Spec (CommRingCat.of k))) :
    IsPGroup p ((SubgroupFunctor.range i).carrier T) := by
  let f := ((yonedaGrp.map i).app (Opposite.op T)).hom
  exact (isPGroup_testPoints_of_isUnipotent p hU T).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective

/-- Bundle the actual pointwise image of a unipotent group with its `p`-group
property, without a choice of a Sylow overgroup. -/
def unipotentPointPSubgroup (hU : IsUnipotent U) (i : U ⟶ G)
    (T : Over (Spec (CommRingCat.of k))) :
    {H : Subgroup (T ⟶ G.X) // IsPGroup p H} :=
  ⟨(SubgroupFunctor.range i).carrier T,
    isPGroup_range_testPoints_of_isUnipotent p hU i T⟩

@[simp] theorem unipotentPointPSubgroup_val (hU : IsUnipotent U) (i : U ⟶ G)
    (T : Over (Spec (CommRingCat.of k))) :
    (unipotentPointPSubgroup p hU i T).val = (SubgroupFunctor.range i).carrier T := rfl

end Langlands.GroupScheme
