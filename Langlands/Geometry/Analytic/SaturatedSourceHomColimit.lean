import Langlands.Geometry.Analytic.SaturatedSourceRefinementEquality
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Yoneda

/-! # The actual source-subatlas Hom quotient and its colimit property -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Actual complete strong numerators, indexed by original-chart selections. -/
abbrev SourceHomRepresentative (A B : SaturatedAtlasPresentation.{u, v, w} K) :=
  Σ P : A.presentation.atlas.RefiningSelection, A.refiningSubpresentation P ⟶ B

/-- The already constructed localization interprets each actual numerator. -/
def sourceHomRepresentativeMap (r : SourceHomRepresentative A B) :
    localizationFunctor.obj A ⟶ localizationFunctor.obj B :=
  localizedRightFraction (sourceRefinementFraction r.1 r.2)

/-- Equality on a further original-chart source is an equivalence relation. -/
def sourceHomSetoid (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Setoid (SourceHomRepresentative A B) where
  r f g := HasCommonSourceRefinement f.2 g.2
  iseqv := {
    refl := fun f => (localizedSourceRefinement_eq_iff f.2 f.2).1 rfl
    symm := fun h => (localizedSourceRefinement_eq_iff _ _).1
      ((localizedSourceRefinement_eq_iff _ _).2 h).symm
    trans := fun h₁ h₂ => (localizedSourceRefinement_eq_iff _ _).1
      (((localizedSourceRefinement_eq_iff _ _).2 h₁).trans
        ((localizedSourceRefinement_eq_iff _ _).2 h₂)) }

/-- A quotient of actual strong numerators on refining original-chart sources. -/
abbrev SourceHomQuotient (A B : SaturatedAtlasPresentation.{u, v, w} K) :=
  Quotient (sourceHomSetoid A B)

/-- The component map from a complete strong Hom type to the quotient. -/
def sourceHomι (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) : SourceHomQuotient A B :=
  Quotient.mk _ ⟨P, f⟩

theorem sourceHomι_eq_iff {P Q : A.presentation.atlas.RefiningSelection}
    (f : A.refiningSubpresentation P ⟶ B) (g : A.refiningSubpresentation Q ⟶ B) :
    sourceHomι P f = sourceHomι Q g ↔ HasCommonSourceRefinement f g :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The quotient component maps are compatible with actual restriction. -/
@[simp]
theorem sourceHomι_restriction {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) (f : A.refiningSubpresentation Q ⟶ B) :
    sourceHomι P (refiningHomRestriction h f) = sourceHomι Q f := by
  apply (sourceHomι_eq_iff _ _).2
  exact ⟨P, le_refl P, h, refiningHomRestriction_id _ _⟩

/-- Descend interpretation of complete numerators to their exact quotient. -/
def sourceHomQuotientMap : SourceHomQuotient A B →
    (localizationFunctor.obj A ⟶ localizationFunctor.obj B) :=
  Quotient.lift sourceHomRepresentativeMap
    (fun _ _ h => (localizedSourceRefinement_eq_iff _ _).2 h)

@[simp]
theorem sourceHomQuotientMap_ι (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    sourceHomQuotientMap (sourceHomι P f) =
      localizedRightFraction (sourceRefinementFraction P f) := rfl

theorem sourceHomQuotientMap_bijective :
    Function.Bijective (sourceHomQuotientMap (A := A) (B := B)) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g h
    exact Quotient.sound ((localizedSourceRefinement_eq_iff f.2 g.2).1 h)
  · intro f
    obtain ⟨P, g, hg, _⟩ := exists_sourceRefinementFraction f
    exact ⟨sourceHomι P g, hg.symm⟩

/-- The source-subatlas quotient computes the actual localization Hom type. -/
def sourceHomEquiv : SourceHomQuotient A B ≃
    (localizationFunctor.obj A ⟶ localizationFunctor.obj B) :=
  Equiv.ofBijective sourceHomQuotientMap sourceHomQuotientMap_bijective

@[simp]
theorem sourceHomEquiv_ι (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    sourceHomEquiv (sourceHomι P f) =
      localizedRightFraction (sourceRefinementFraction P f) := rfl

/-- The quotient comparison retains the exact continuous numerator map. -/
theorem localizedSpaceFunctor_map_sourceHomEquiv_ι
    (P : A.presentation.atlas.RefiningSelection) (f : A.refiningSubpresentation P ⟶ B) :
    localizedSpaceFunctor.map (sourceHomEquiv (sourceHomι P f)) =
      TopCat.ofHom f.baseMap :=
  localizedSpaceFunctor_map_sourceRefinementFraction P f

/-- A family compatible with actual restriction, with independently sized target. -/
def SourceHomCompatible {Z : Type z}
    (φ : ∀ P : A.presentation.atlas.RefiningSelection,
      (A.refiningSubpresentation P ⟶ B) → Z) : Prop :=
  ∀ (P Q : A.presentation.atlas.RefiningSelection) (h : P ≤ Q)
    (f : A.refiningSubpresentation Q ⟶ B), φ P (refiningHomRestriction h f) = φ Q f

/-- Descend a compatible family using complete equality on a common source. -/
def sourceHomDesc {Z : Type z}
    (φ : ∀ P : A.presentation.atlas.RefiningSelection,
      (A.refiningSubpresentation P ⟶ B) → Z)
    (hφ : SourceHomCompatible φ) : SourceHomQuotient A B → Z :=
  Quotient.lift (fun r => φ r.1 r.2) (by
    intro f g h
    obtain ⟨R, hRP, hRQ, heq⟩ := h
    exact (hφ R f.1 hRP f.2).symm.trans
      ((congrArg (φ R) heq).trans (hφ R g.1 hRQ g.2)))

@[simp]
theorem sourceHomDesc_ι {Z : Type z}
    (φ : ∀ P : A.presentation.atlas.RefiningSelection,
      (A.refiningSubpresentation P ⟶ B) → Z)
    (hφ : SourceHomCompatible φ) (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    sourceHomDesc φ hφ (sourceHomι P f) = φ P f := rfl

theorem sourceHomDesc_unique {Z : Type z}
    (φ : ∀ P : A.presentation.atlas.RefiningSelection,
      (A.refiningSubpresentation P ⟶ B) → Z)
    (hφ : SourceHomCompatible φ) (m : SourceHomQuotient A B → Z)
    (hm : ∀ P f, m (sourceHomι P f) = φ P f) :
    m = sourceHomDesc φ hφ := by
  funext x
  refine Quotient.inductionOn x ?_
  intro r
  exact hm r.1 r.2

/-- The actual Hom diagram is contravariant in inclusion of source selections. -/
def sourceHomDiagram (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    A.presentation.atlas.RefiningSelectionᵒᵖ ⥤ Type (max u v w) :=
  (A.refiningSubatlasFunctor).op ⋙ yoneda.obj B

@[simp]
theorem sourceHomDiagram_map {P Q : A.presentation.atlas.RefiningSelection}
    (h : P ≤ Q) (f : A.refiningSubpresentation Q ⟶ B) :
    (sourceHomDiagram A B).map (homOfLE h).op f = refiningHomRestriction h f := rfl

/-- Intersections of refining selections make the Hom diagram's index filtered. -/
theorem sourceHomDiagram_index_filtered (A : SaturatedAtlasPresentation.{u, v, w} K) :
    IsFiltered A.presentation.atlas.RefiningSelectionᵒᵖ := by infer_instance

/-- The exact quotient cocone on the actual strong Hom diagram. -/
def sourceHomCocone (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Cocone (sourceHomDiagram A B) where
  pt := SourceHomQuotient A B
  ι := {
    app := fun P => TypeCat.ofHom (sourceHomι P.unop)
    naturality := by
      intro P Q h
      ext f
      exact sourceHomι_restriction (leOfHom h.unop) f }

/-- Every cocone supplies a restriction-compatible family of functions. -/
theorem sourceHomCocone_compatible (s : Cocone (sourceHomDiagram A B)) :
    SourceHomCompatible (fun P f => s.ι.app (op P) f) := by
  intro P Q h f
  exact congrArg (fun k => k f) (s.w (homOfLE h).op)

/-- The quotient satisfies the categorical colimit universal property. -/
def sourceHomIsColimit (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    IsColimit (sourceHomCocone A B) where
  desc s := TypeCat.ofHom
    (sourceHomDesc (fun P f => s.ι.app (op P) f) (sourceHomCocone_compatible s))
  fac s P := by
    ext f
    rfl
  uniq s m hm := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    apply sourceHomDesc_unique _ (sourceHomCocone_compatible s)
    intro P f
    exact congrArg (fun k => k f) (hm (op P))

end Langlands.Analytic.SaturatedAtlasPresentation
