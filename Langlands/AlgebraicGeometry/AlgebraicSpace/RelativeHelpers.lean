import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors

/-! # Relative morphism properties of presheaves: composition and Yoneda images

Composition and isomorphism invariance for relative etale maps and open immersions of
presheaves on schemes over a base, Yoneda images of etale scheme morphisms, ranges of open
immersions from affine schemes, and finite intersections of dense open sets.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open OpenSubfunctorLifting AffineOpenSubfunctors

section Relative

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}}

local instance : (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).RespectsIso := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) := Etale.etale_isStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

local instance : (MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget S)).IsStableUnderComposition := by
  have h : MorphismProperty.IsMultiplicative (@Etale.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    h.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @Etale.{u}) (Over.forget S)

local instance : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (Over.forget S)).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ _

local instance : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (Over.forget S)).IsStableUnderComposition := by
  have h : MorphismProperty.IsMultiplicative (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) :=
    inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) := h.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)

variable {F G H : Presheaf S}

theorem IsEtale.comp_iso {f : F ⟶ G} (hf : IsEtale f) (e : G ≅ H) : IsEtale (f ≫ e.hom) :=
  (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr hf

theorem IsEtale.iso_comp (e : F ≅ G) {g : G ⟶ H} (hg : IsEtale g) : IsEtale (e.hom ≫ g) :=
  (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative
      (schemeYoneda S)) _ _).mpr hg

theorem IsOpenImmersion.comp' {f : F ⟶ G} {g : G ⟶ H} (hf : IsOpenImmersion f)
    (hg : IsOpenImmersion g) : IsOpenImmersion (f ≫ g) :=
  MorphismProperty.comp_mem ((MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)).relative
    (schemeYoneda S)) f g hf hg

theorem IsOpenImmersion.iso_comp (e : F ≅ G) {g : G ⟶ H} (hg : IsOpenImmersion g) :
    IsOpenImmersion (e.hom ≫ g) :=
  (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)) _ _).mpr hg

theorem IsOpenImmersion.comp_iso {f : F ⟶ G} (hf : IsOpenImmersion f) (e : G ≅ H) :
    IsOpenImmersion (f ≫ e.hom) :=
  (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)) _ _).mpr hf

/-- The range of an open immersion from an affine scheme is an affine open subfunctor. -/
theorem isAffineOpen_range {V : Over S} [IsAffine V.left] (f : (schemeYoneda S).obj V ⟶ F)
    (hf : IsOpenImmersion f) : IsAffineOpen (Subfunctor.range f) := by
  have : Mono f := SliceOpenGluing.open_mono hf
  exact ⟨range_open f hf, V, inferInstance, ⟨asIso (Subfunctor.toRange f)⟩⟩

end Relative

/-- A finite intersection of dense open sets is dense. -/
theorem dense_iInter_of_isOpen_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {f : ι → Set X} (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) : Dense (⋂ i, f i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, Dense (⋂ i ∈ s, f i) ∧ IsOpen (⋂ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [dense_univ]
    | insert a s ha ih =>
      rw [Finset.set_biInter_insert]
      exact ⟨(hd a).inter_of_isOpen_left ih.1 (ho a), (ho a).inter ih.2⟩
  simpa using (key Finset.univ).1

end Langlands.AlgebraicGeometry.AlgebraicSpace
