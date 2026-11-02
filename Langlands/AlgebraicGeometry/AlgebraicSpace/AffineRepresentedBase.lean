import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Scheme extraction over a represented base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The actual scheme obtained by base change along the identity of a
represented target. -/
def IsRepresentableMorphism.representingScheme
    {S : Scheme.{u}} {F : Presheaf S} {B : Over S}
    {f : F ⟶ (schemeYoneda S).obj B} (hf : IsRepresentableMorphism f) : Over S :=
  hf.pullback (𝟙 _)

/-- A relatively representable morphism to a represented base has a represented
source, with the original map induced by an actual morphism of schemes. -/
theorem IsRepresentableMorphism.exists_representation_over
    {S : Scheme.{u}} {F : Presheaf S} {B : Over S}
    {f : F ⟶ (schemeYoneda S).obj B} (hf : IsRepresentableMorphism f) :
    ∃ (V : Over S) (p : V ⟶ B) (e : (schemeYoneda S).obj V ≅ F),
      e.hom ≫ f = (schemeYoneda S).map p := by
  let g : (schemeYoneda S).obj B ⟶ (schemeYoneda S).obj B := 𝟙 _
  have h := hf.isPullback g
  let : IsIso (hf.fst g) := h.isIso_fst_of_isIso
  exact ⟨hf.pullback g, hf.snd g, asIso (hf.fst g), by simpa [g] using h.w⟩

/-- Affine, locally finitely presented morphisms to represented bases are
represented by actual affine, locally finitely presented scheme morphisms. -/
theorem IsAffineMorphism.exists_representation_over
    {S : Scheme.{u}} {F : Presheaf S} {B : Over S}
    {f : F ⟶ (schemeYoneda S).obj B} (hf : IsAffineMorphism f)
    (hfp : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
      (Over.forget S)).relative (schemeYoneda S) f) :
    ∃ (V : Over S) (p : V ⟶ B) (e : (schemeYoneda S).obj V ≅ F),
      e.hom ≫ f = (schemeYoneda S).map p ∧
      IsAffineHom p.left ∧ LocallyOfFinitePresentation p.left := by
  let hr : IsRepresentableMorphism f := hf.rep
  let g : (schemeYoneda S).obj B ⟶ (schemeYoneda S).obj B := 𝟙 _
  have h := hr.isPullback g
  let : IsIso (hr.fst g) := h.isIso_fst_of_isIso
  refine ⟨hr.pullback g, hr.snd g, asIso (hr.fst g), ?_, ?_, ?_⟩
  · simpa [g] using h.w
  · exact hf.property g _ _ h
  · exact hfp.property g _ _ h

/-- At the terminal represented base the extracted projection is the structure
map of an actual scheme over the base scheme. -/
theorem IsAffineMorphism.exists_representation
    {S : Scheme.{u}} {F : Presheaf S}
    {f : F ⟶ (schemeYoneda S).obj (Over.mk (𝟙 S))}
    (hf : IsAffineMorphism f)
    (hfp : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
      (Over.forget S)).relative (schemeYoneda S) f) :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F) ∧
      IsAffineHom V.hom ∧ LocallyOfFinitePresentation V.hom := by
  obtain ⟨V, p, e, _, ha, hp⟩ := hf.exists_representation_over hfp
  have h : p.left = V.hom := by simpa using p.w
  exact ⟨V, ⟨e⟩, h ▸ ha, h ▸ hp⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
