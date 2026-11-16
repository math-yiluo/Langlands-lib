import Langlands.Algebra.SemilocalFiniteAlgebra
import Langlands.GroupScheme.Torus.WeilRestrictionPicardCocycle

/-! # Cocycle vanishing through Weil-restriction presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {G : GroupScheme (Spec A)} {U : Over (Spec A)}
  [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
  (ξ : Cocycle G U) (e : G ≅ WeilGm.groupScheme A B)

section Picard

variable [Subsingleton (CommRing.Pic B)]

/-- Transfer the Picard coboundary across an actual WeilGm presentation. -/
def weilPresentationPicardCochain : U ⟶ G.X :=
  (ξ.map e.hom).weilPicardCochain ≫ e.inv.hom.hom

/-- The transferred cochain cobounds the original cocycle on every test. -/
theorem weilPresentationPicardCochain_spec {Z : Over (Spec A)} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.weilPresentationPicardCochain e) *
      (b ≫ ξ.weilPresentationPicardCochain e)⁻¹ := by
  have h := congrArg (fun x : Z ⟶ (WeilGm.groupScheme A B).X =>
    x ≫ e.inv.hom.hom) ((ξ.map e.hom).weilPicardCochain_spec a b)
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun q : G ⟶ G => q.hom.hom) e.hom_inv_id
  simpa only [map, Category.assoc, he, Category.comp_id, MonObj.mul_comp,
    GrpObj.inv_comp, weilPresentationPicardCochain] using h

include e in
/-- Picard triviality kills cocycles under an actual WeilGm presentation. -/
theorem isTrivial_of_weilPresentation_of_pic_trivial : ξ.IsTrivial :=
  ⟨ξ.weilPresentationPicardCochain e, ξ.weilPresentationPicardCochain_spec e⟩

end Picard

include e in
/-- Trivial Picard groups of finite algebras suffice for every supplied
finite-projective WeilGm presentation. -/
theorem isTrivial_of_weilPresentation_of_finiteAlgebrasHaveTrivialPicard
    (hA : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} A) :
    ξ.IsTrivial := by
  let : Subsingleton (CommRing.Pic B) := hA B
  exact ξ.isTrivial_of_weilPresentation_of_pic_trivial e

include e in
/-- Over a semi-local ring, cocycles under a finite-projective WeilGm presentation
are trivial on the original affine faithfully flat cover. -/
theorem isTrivial_of_weilPresentation_of_semilocal [Finite (MaximalSpectrum A)] :
    ξ.IsTrivial :=
  ξ.isTrivial_of_weilPresentation_of_finiteAlgebrasHaveTrivialPicard e
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal A)

/-- The canonical WeilGm specialization over a semi-local base. -/
theorem isTrivial_weil_of_semilocal [Finite (MaximalSpectrum A)]
    (ζ : Cocycle (WeilGm.groupScheme A B) U) : ζ.IsTrivial :=
  ζ.isTrivial_of_weilPresentation_of_semilocal (Iso.refl _)

end Langlands.GroupScheme.Cocycle
