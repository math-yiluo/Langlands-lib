import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Transport of scheme atlases along presheaf isomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G H : Presheaf S}

/-- Composing a representable geometrically surjective transformation with a
presheaf isomorphism preserves geometric surjectivity. -/
theorem IsSurjective.comp_iso {f : F ⟶ G} (hf : IsSurjective f) (e : G ≅ H) :
    IsSurjective (f ≫ e.hom) := by
  let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u}) (Over.forget S)
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr hf

/-- Scheme representability of the diagonal is preserved by a full natural
isomorphism of presheaves. -/
theorem hasRepresentableDiagonal_of_iso (e : F ≅ G) (hF : HasRepresentableDiagonal F) :
    HasRepresentableDiagonal G := by
  have hw : Limits.diag G =
      e.inv ≫ Limits.diag F ≫ (prod.mapIso e e).hom := by
    rw [← Category.assoc, ← Limits.prod.diag_map]
    simp
  rw [HasRepresentableDiagonal, IsRepresentableMorphism, hw]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (schemeYoneda S).relativelyRepresentable _ _).mpr
    ((MorphismProperty.cancel_right_of_respectsIso
      (schemeYoneda S).relativelyRepresentable _ _).mpr hF)

/-- Every relative scheme-morphism property respecting isomorphisms transfers
from the full diagonal of a presheaf to that of an isomorphic presheaf. -/
theorem relative_diag_of_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (e : F ≅ G)
    (hF : (MorphismProperty.inverseImage P (Over.forget S)).relative
      (schemeYoneda S) (Limits.diag F)) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative
      (schemeYoneda S) (Limits.diag G) := by
  let := MorphismProperty.RespectsIso.inverseImage P (Over.forget S)
  have hw : Limits.diag G =
      e.inv ≫ Limits.diag F ≫ (prod.mapIso e e).hom := by
    rw [← Category.assoc, ← Limits.prod.diag_map]
    simp
  rw [hw]
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage P (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr
    ((MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage P (Over.forget S)).relative
        (schemeYoneda S)) _ _).mpr hF)

/-- A locally finite type etale-surjective scheme atlas transfers along a
full natural isomorphism, keeping its actual source scheme. -/
theorem exists_locallyFiniteType_atlas_of_iso (e : F ≅ G)
    (hF : ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F),
      IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ G),
      IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom := by
  obtain ⟨U, a, ha, hs, hU⟩ := hF
  exact ⟨U, a ≫ e.hom, ha.comp_iso e, hs.comp_iso e, hU⟩

/-- The algebraic-space conditions for an actual fppf sheaf transfer along
an isomorphism of its full underlying presheaf. -/
theorem isAlgebraicSpace_of_presheafIso {A B : FppfSheaf S}
    (e : A.obj ≅ B.obj) (hA : IsAlgebraicSpace S A) :
    IsAlgebraicSpace S B := by
  obtain ⟨hD, U, a, ha, hs⟩ := hA
  exact ⟨hasRepresentableDiagonal_of_iso e hD, U, a ≫ e.hom,
    ha.comp_iso e, hs.comp_iso e⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
