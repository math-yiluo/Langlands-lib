import Langlands.GroupScheme.Rational.NormalRadicalConjugacy
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.RepresentedSubgroupTransport

/-! # Whole-torus centralizers under isomorphism squares -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' L : GroupScheme S}
  {A B : CommGroupScheme S}

/-- A square with source and ambient isomorphisms transports the whole-group
centralizer, including all relative tests and refinements. -/
theorem torusCentralizer_eq_comap_of_iso_square
    (a : A.toGrp ⟶ G) (b : B.toGrp ⟶ G')
    (e : A.toGrp ≅ B.toGrp) (f : G ≅ G')
    (h : a ≫ f.hom = e.hom ≫ b) :
    torusCentralizer a = (torusCentralizer b).comap f.hom := by
  rw [torusCentralizer_eq_comap_of_iso a f]
  rw [torusCentralizer_eq_of_iso (a ≫ f.hom) b e h.symm]

/-- An isomorphism square transports a specified representative of the full
centralizer by the ambient isomorphism. -/
theorem SubgroupFunctor.IsRepresentedBy.torusCentralizer_of_iso_square
    {a : A.toGrp ⟶ G} {b : B.toGrp ⟶ G'} {l : L ⟶ G}
    (hl : (torusCentralizer a).IsRepresentedBy l)
    (e : A.toGrp ≅ B.toGrp) (f : G ≅ G')
    (h : a ≫ f.hom = e.hom ≫ b) :
    (torusCentralizer b).IsRepresentedBy (l ≫ f.hom) := by
  have hr := hl.comp_iso f
  change ((torusCentralizer a).comap f.inv).IsRepresentedBy (l ≫ f.hom) at hr
  rwa [torusCentralizer_eq_comap_of_iso_square a b e f h,
    SubgroupFunctor.comap_iso_hom_inv] at hr

end Langlands.GroupScheme
