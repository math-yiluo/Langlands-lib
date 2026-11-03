import Langlands.GroupScheme.Rational.TorusSplitPart
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Restricting conjugacy of commutative overgroups to maximal split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {H T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The isomorphism between maximal split tori of a commutative affine group
locally of finite type, obtained from their largest-subtorus universal properties. -/
def IsMaximalSplitTorus.isoOverCommGroup
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    {i : T.toGrp ⟶ H.toGrp} {i' : T'.toGrp ⟶ H.toGrp}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    T.toGrp ≅ T'.toGrp :=
  Classical.choose (hi.isLargestSplitSubtorus.unique hi'.isLargestSplitSubtorus)

@[simp]
theorem IsMaximalSplitTorus.isoOverCommGroup_hom_comp
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    {i : T.toGrp ⟶ H.toGrp} {i' : T'.toGrp ⟶ H.toGrp}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    (hi.isoOverCommGroup hi').hom ≫ i' = i :=
  Classical.choose_spec (hi.isLargestSplitSubtorus.unique hi'.isLargestSplitSubtorus)

/-- The maximal split tori of a commutative affine group locally of finite type
are rationally conjugate by its identity point. -/
theorem subgroupConjugate_of_commGroup
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
    {i : T.toGrp ⟶ H.toGrp} {i' : T'.toGrp ⟶ H.toGrp}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    SubgroupConjugate i i' := by
  refine ⟨1, hi.isoOverCommGroup hi', ?_⟩
  rw [innerIso_one_hom, Category.comp_id, hi.isoOverCommGroup_hom_comp hi']

/-- If two ambient maximal split tori factor through rationally conjugate
commutative closed subgroups, they are rationally conjugate in the ambient group. -/
theorem subgroupConjugate_of_conjugate_commutative_overgroups
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {H' : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (j : H.toGrp ⟶ G) (j' : H'.toGrp ⟶ G)
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j')
    (f : T.toGrp ⟶ H.toGrp) (f' : T'.toGrp ⟶ H'.toGrp)
    (hf : f ≫ j = i) (hf' : f' ≫ j' = i')
    (hc : SubgroupConjugate j j') :
    SubgroupConjugate i i' := by
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have : IsAffine H'.X.left := isAffine_of_isAffineHom j'.hom.hom.left
  have : LocallyOfFiniteType H'.X.hom := by
    rw [← Over.w j'.hom.hom]
    infer_instance
  have hfi : IsMaximalSplitTorus f :=
    IsMaximalSplitTorus.of_comp hj (hf.symm ▸ hi)
  have hfi' : IsMaximalSplitTorus f' :=
    IsMaximalSplitTorus.of_comp hj' (hf'.symm ▸ hi')
  obtain ⟨g, e, he⟩ := hc
  have hInside : SubgroupConjugate (f ≫ e.hom) f' :=
    subgroupConjugate_of_commGroup (hfi.comp_iso e) hfi'
  simpa only [hf, hf'] using
    SubgroupConjugate.of_overgroups j j' f f' g e he hInside

end Langlands.GroupScheme
