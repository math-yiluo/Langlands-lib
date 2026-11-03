import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Represented subgroup schemes under ambient isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy

variable {B : Scheme.{u}} {G G' H H' : GroupScheme B}
    {F : SubgroupFunctor G} {K : SubgroupFunctor G'} {i : H ⟶ G} {j : H' ⟶ G'}

/-- A full subgroup comparison under an ambient isomorphism identifies the
supplied representing group schemes, compatibly with their inclusions. -/
def isoOfComap (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F) : H ≅ H' :=
  hi.isoOfIsRepresentedBy (by
    have hr := hj.comp_iso e.symm
    change (K.comap e.hom).IsRepresentedBy (j ≫ e.inv) at hr
    rwa [h] at hr)

@[reassoc] theorem isoOfComap_hom_comp
    (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F) :
    (isoOfComap hi hj e h).hom ≫ j = i ≫ e.hom := by
  apply (Iso.comp_inv_eq e).1
  rw [Category.assoc]
  exact isoOfIsRepresentedBy_hom_comp hi
    (by
      have hr := hj.comp_iso e.symm
      change (K.comap e.hom).IsRepresentedBy (j ≫ e.inv) at hr
      rwa [h] at hr)

@[reassoc] theorem isoOfComap_inv_comp
    (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F) :
    (isoOfComap hi hj e h).inv ≫ i = j ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, isoOfComap_hom_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inclusion square determines this isomorphism uniquely. -/
theorem isoOfComap_unique
    (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F)
    (q : H ≅ H') (hq : q.hom ≫ j = i ≫ e.hom) :
    q = isoOfComap hi hj e h := by
  apply Iso.ext
  exact hj.hom_ext (hq.trans (isoOfComap_hom_comp hi hj e h).symm)

/-- On every scheme test the forward comparison is the original ambient map. -/
theorem isoOfComap_hom_points
    (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F)
    {U : Over B} (x : U ⟶ H.X) :
    (x ≫ (isoOfComap hi hj e h).hom.hom.hom) ≫ j.hom.hom =
      (x ≫ i.hom.hom) ≫ e.hom.hom.hom := by
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun k => x ≫ k.hom.hom) (isoOfComap_hom_comp hi hj e h)

/-- The inverse comparison is the original inverse ambient map on every test. -/
theorem isoOfComap_inv_points
    (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (e : G ≅ G') (h : K.comap e.hom = F)
    {U : Over B} (x : U ⟶ H'.X) :
    (x ≫ (isoOfComap hi hj e h).inv.hom.hom) ≫ i.hom.hom =
      (x ≫ j.hom.hom) ≫ e.inv.hom.hom := by
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun k => x ≫ k.hom.hom) (isoOfComap_inv_comp hi hj e h)

end Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy
