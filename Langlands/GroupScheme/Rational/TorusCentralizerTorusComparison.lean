import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Comparing a maximal torus with a torus representative of a centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ G} {i : T.toGrp ⟶ G}

/-- A supplied maximal torus containing a commutative subgroup is isomorphic
to any closed torus representing the centralizer of that subgroup. -/
def IsMaximalTorus.isoTorusCentralizer
    (hi : IsMaximalTorus i) (f : A.toGrp ⟶ T.toGrp) (hf : f ≫ i = a)
    (j : C ⟶ G) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hC : IsTorus C) : T.toGrp ≅ C := by
  let q := hj.factorHom i (range_le_torusCentralizer_of_factor a i f hf)
  have hq : q ≫ j = i := hj.factorHom_comp _ _
  have hqm : IsMaximalTorus q := by
    apply IsMaximalTorus.of_comp hjc
    rwa [hq]
  letI : IsIso q := hqm.isIso_of_torus hC
  exact asIso q

/-- The comparison isomorphism recovers the original maximal-torus inclusion. -/
@[simp]
theorem IsMaximalTorus.isoTorusCentralizer_hom_comp
    (hi : IsMaximalTorus i) (f : A.toGrp ⟶ T.toGrp) (hf : f ≫ i = a)
    (j : C ⟶ G) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hC : IsTorus C) :
    (hi.isoTorusCentralizer f hf j hj hjc hC).hom ≫ j = i :=
  hj.factorHom_comp _ _

/-- The comparison is the unique isomorphism compatible with the original
inclusion and the chosen centralizer representative. -/
theorem IsMaximalTorus.isoTorusCentralizer_unique
    (hi : IsMaximalTorus i) (f : A.toGrp ⟶ T.toGrp) (hf : f ≫ i = a)
    (j : C ⟶ G) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hC : IsTorus C) (e : T.toGrp ≅ C)
    (he : e.hom ≫ j = i) :
    e = hi.isoTorusCentralizer f hf j hj hjc hC := by
  apply Iso.ext
  exact hj.hom_ext (he.trans (hi.isoTorusCentralizer_hom_comp f hf j hj hjc hC).symm)

/-- If the centralizer has a closed torus representative, every supplied
maximal torus containing the subgroup represents that centralizer on all tests. -/
theorem IsMaximalTorus.isRepresentedBy_torusCentralizer_of_isTorus
    (hi : IsMaximalTorus i) (f : A.toGrp ⟶ T.toGrp) (hf : f ≫ i = a)
    (j : C ⟶ G) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hC : IsTorus C) :
    (torusCentralizer a).IsRepresentedBy i := by
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  calc
    SubgroupFunctor.range i =
        SubgroupFunctor.range ((hi.isoTorusCentralizer f hf j hj hjc hC).hom ≫ j) :=
      congrArg SubgroupFunctor.range (hi.isoTorusCentralizer_hom_comp f hf j hj hjc hC).symm
    _ = SubgroupFunctor.range j :=
      SubgroupFunctor.range_iso_comp (hi.isoTorusCentralizer f hf j hj hjc hC) j
    _ = torusCentralizer a := hj.2

end Langlands.GroupScheme
