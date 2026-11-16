import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.Torus.PicardTrivialCocycle
import Langlands.GroupScheme.Torus.WeilRestrictionSemilocalCocycle

/-! # Picard-trivial torus cocycles on arbitrary single fppf covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {G : GroupScheme (Spec A)} {U : Over (Spec A)}
  [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
  (ξ : Cocycle G U) (e : G ≅ WeilGm.groupScheme A B)

section WeilPicard

variable [Subsingleton (CommRing.Pic B)]

include e in
/-- A supplied finite-projective WeilGm presentation has trivial cocycles on
arbitrary single fppf covers when the coefficient ring has trivial Picard group. -/
theorem isTrivial_of_weilPresentation_fppf_of_pic_trivial : ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact ζ.isTrivial_of_weilPresentation_of_pic_trivial e

/-- Choose a Picard coboundary on the original, possibly non-quasi-compact
single fppf cover. -/
def weilPresentationFppfPicardCochain : U ⟶ G.X :=
  Classical.choose (ξ.isTrivial_of_weilPresentation_fppf_of_pic_trivial e)

/-- The original-cover cochain cobounds the cocycle on every test scheme. -/
theorem weilPresentationFppfPicardCochain_spec {Z : Over (Spec A)}
    (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.weilPresentationFppfPicardCochain e) *
      (b ≫ ξ.weilPresentationFppfPicardCochain e)⁻¹ :=
  Classical.choose_spec (ξ.isTrivial_of_weilPresentation_fppf_of_pic_trivial e) a b

/-- The canonical WeilGm specialization of Picard-trivial fppf cocycle vanishing. -/
theorem isTrivial_weil_fppf_of_pic_trivial
    (ζ : Cocycle (WeilGm.groupScheme A B) U) : ζ.IsTrivial :=
  ζ.isTrivial_of_weilPresentation_fppf_of_pic_trivial (Iso.refl _)

end WeilPicard

include e in
/-- Trivial Picard groups of all finite algebras imply vanishing under a supplied
WeilGm presentation, for arbitrary single fppf covers. -/
theorem isTrivial_of_weilPresentation_fppf_of_finiteAlgebrasHaveTrivialPicard
    (hA : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} A) :
    ξ.IsTrivial := by
  let : Subsingleton (CommRing.Pic B) := hA B
  exact ξ.isTrivial_of_weilPresentation_fppf_of_pic_trivial e

include e in
/-- Over a semi-local ring, finite-projective WeilGm-presentation cocycles on any
single fppf cover are trivial on the original cover. -/
theorem isTrivial_of_weilPresentation_fppf_of_semilocal [Finite (MaximalSpectrum A)] :
    ξ.IsTrivial :=
  ξ.isTrivial_of_weilPresentation_fppf_of_finiteAlgebrasHaveTrivialPicard e
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal A)

/-- The canonical WeilGm specialization over a semi-local ring. -/
theorem isTrivial_weil_fppf_of_semilocal [Finite (MaximalSpectrum A)]
    (ζ : Cocycle (WeilGm.groupScheme A B) U) : ζ.IsTrivial :=
  ζ.isTrivial_of_weilPresentation_fppf_of_semilocal (Iso.refl _)

section Split

variable {I : Type u} [Finite I] [Subsingleton (CommRing.Pic A)]
  (ζ : Cocycle (splitTorus (Spec A) I) U)

/-- Split-torus cocycles vanish on arbitrary single fppf covers of a
Picard-trivial affine base. -/
theorem isTrivial_split_fppf_of_pic_trivial : ζ.IsTrivial := by
  apply ζ.isTrivial_of_affine_fppf
  intro W _ _ _ _ coc
  exact coc.isTrivial_split_of_pic_trivial

/-- Choose an original-cover split-torus Picard cochain. -/
def splitFppfPicardCochain : U ⟶ (splitTorus (Spec A) I).X :=
  Classical.choose ζ.isTrivial_split_fppf_of_pic_trivial

/-- The split-torus cochain has the all-test coboundary equation. -/
theorem splitFppfPicardCochain_spec {Z : Over (Spec A)} (a b : Z ⟶ U) :
    ζ.toFun a b = (a ≫ ζ.splitFppfPicardCochain) *
      (b ≫ ζ.splitFppfPicardCochain)⁻¹ :=
  Classical.choose_spec ζ.isTrivial_split_fppf_of_pic_trivial a b

end Split

end Langlands.GroupScheme.Cocycle
