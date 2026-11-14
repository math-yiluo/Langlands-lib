import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleLocality
import Langlands.GroupScheme.Descent.MonicSubgroups

/-! # Effective descent of invariant parabolics over affine étale covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Descent

/-- An invariant relative parabolic over a surjective étale map of affine
schemes descends to an actual relative parabolic, with exact pullback recovery. -/
theorem IsRelativeParabolicSubgroup.exists_descent_of_overlap_range_eq
    {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
    [Etale p] [Surjective p] {C : GroupScheme B} (hC : IsReductive C)
    {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj C}
    (hi : IsRelativeParabolicSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p C).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    ∃ (H₀ : GroupScheme B) (j : H₀ ⟶ C) (e : (GroupScheme.baseChange p).obj H₀ ≅ H),
      IsRelativeParabolicSubgroup j ∧
        (GroupScheme.baseChange p).map j = e.hom ≫ i := by
  let : IsAffineHom H.X.hom := hi.isAffineHom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Mono i.hom.hom := hi.mono
  obtain ⟨H₀, j, e, _, _, he⟩ := exists_affine_monic_descent_of_overlap_range_eq p h
  refine ⟨H₀, j, e, ?_, he⟩
  apply IsRelativeParabolicSubgroup.of_etale_surjective hC p j
  rw [he]
  exact hi.iso_comp e

namespace ParabolicSubgroupModuli

/-- A supplied monic representative is parabolic if its pullback is parabolic
along a surjective étale cover. -/
theorem isParabolic_of_isRepresentedBy_of_etale_surjective
    {B S : Scheme.{u}} (p : S ⟶ B) [Etale p] [Surjective p]
    {C : GroupScheme B} (hC : IsReductive C) {F : SubgroupFunctor C}
    {H : GroupScheme B} {j : H ⟶ C} (hj : F.IsRepresentedBy j)
    (h : IsParabolic (F.baseChange p)) : IsParabolic F := by
  let r := parabolicRepresentative ⟨F.baseChange p, h⟩
  let e := (hj.baseChange p).isoOfIsRepresentedBy r.represents
  have he : e.hom ≫ r.hom = (GroupScheme.baseChange p).map j :=
    (hj.baseChange p).isoOfIsRepresentedBy_hom_comp r.represents
  refine ⟨H, j, IsRelativeParabolicSubgroup.of_etale_surjective hC p j ?_, hj⟩
  simpa only [he] using r.parabolic.iso_comp e

/-- An invariant relative parabolic over an affine étale cover determines
exactly one actual parabolic subgroup functor over the base. -/
theorem existsUnique_of_overlap_range_eq
    {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
    [Etale p] [Surjective p] {C : GroupScheme B} (hC : IsReductive C)
    {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj C}
    (hi : IsRelativeParabolicSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p C).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    ∃! F : ParabolicSubgroup C, F.val.baseChange p = SubgroupFunctor.range i := by
  obtain ⟨H₀, j, e, hj, he⟩ := hi.exists_descent_of_overlap_range_eq p hC h
  let F : ParabolicSubgroup C := ⟨SubgroupFunctor.range j, isParabolic_range j hj⟩
  have hF : F.val.baseChange p = SubgroupFunctor.range i := by
    rw [← SubgroupFunctor.range_baseChangeHom, he, SubgroupFunctor.range_iso_comp]
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  apply (baseChangeEmbedding hC p).injective
  exact Subtype.ext (hF'.trans hF.symm)

section

variable {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
  [Etale p] [Surjective p] {C : GroupScheme B} (hC : IsReductive C)
  {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj C}
  (hi : IsRelativeParabolicSubgroup i)
  (h : SubgroupFunctor.range
      ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p C).hom) =
    SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i))

/-- The actual parabolic subgroup descended from an invariant inclusion over
an affine surjective étale cover. -/
def descendAffineEtale : ParabolicSubgroup C :=
  (existsUnique_of_overlap_range_eq p hC hi h).choose

/-- Pullback of the descended subgroup is exactly the supplied local range. -/
@[simp]
theorem descendAffineEtale_baseChange :
    (descendAffineEtale p hC hi h).val.baseChange p = SubgroupFunctor.range i :=
  (existsUnique_of_overlap_range_eq p hC hi h).choose_spec.1

/-- Every parabolic with the prescribed pullback equals the constructed descent. -/
theorem eq_descendAffineEtale {F : ParabolicSubgroup C}
    (hF : F.val.baseChange p = SubgroupFunctor.range i) :
    F = descendAffineEtale p hC hi h :=
  (existsUnique_of_overlap_range_eq p hC hi h).choose_spec.2 F hF

end

end ParabolicSubgroupModuli

end Langlands.GroupScheme
