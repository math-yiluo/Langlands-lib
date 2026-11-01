import Langlands.Geometry.Analytic.AtlasInducedUniversal
import Langlands.Geometry.Analytic.NonemptyAtlasActions
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Induction adjunction on full nonempty-chart atlas action categories -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)

/-- The constructed coset atlas has nonempty spectra on every supplied chart. -/
theorem copies_hasNonemptyCharts
    (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H) :
    (copies H X).atlas.HasNonemptyCharts :=
  AtlasDisjointUnion.atlas_hasNonemptyCharts _ _

/-- Lift actual coset-copy induction to the full nonempty-chart categories. -/
def nonemptyCopiesFunctor :
    NonemptyAtlasAction.{u, max z v, max z w, z} K H ⥤
      NonemptyAtlasAction.{u, max z v, max z w, z} K G :=
  (nonemptyAtlasActionProperty K G).lift
    (NonemptyAtlasAction.inclusion ⋙ copiesFunctor H)
    (fun X => copies_hasNonemptyCharts H X.obj)

@[simp]
theorem nonemptyCopiesFunctor_obj
    (X : NonemptyAtlasAction.{u, max z v, max z w, z} K H) :
    ((nonemptyCopiesFunctor H).obj X).obj = copiesAction H X.obj := rfl

@[simp]
theorem nonemptyCopiesFunctor_map
    {X X' : NonemptyAtlasAction.{u, max z v, max z w, z} K H} (a : X' ⟶ X) :
    ((nonemptyCopiesFunctor H).map a).hom = copiesEquivariantMap H a.hom := rfl

variable (X X' : NonemptyAtlasAction.{u, max z v, max z w, z} K H)
  (Y Z : NonemptyAtlasAction.{u, max z v, max z w, z} K G)

/-- Original-source Hom correspondence using the constructed normalization inverse. -/
def nonemptyHomEquiv :
    ((nonemptyCopiesFunctor H).obj X ⟶ Y) ≃
      (X ⟶ (NonemptyAtlasAction.restrict H.subtype).obj Y) where
  toFun p := ObjectProperty.homMk
    ((NonemptyAtlasAction.normalizationIso X).inv ≫ actionExtensionEquiv H p.hom)
  invFun f := ObjectProperty.homMk
    (extendToAction H ((NonemptyAtlasAction.normalizationIso X).hom ≫ f.hom))
  left_inv p := by
    apply ObjectProperty.hom_ext
    let p₀ : copiesAction H X.obj ⟶ Y.obj := p.hom
    change extendToAction H ((NonemptyAtlasAction.normalizationIso X).hom ≫
      ((NonemptyAtlasAction.normalizationIso X).inv ≫ restrictFromAction H p₀)) = p₀
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      extendToAction_restrictFromAction]
  right_inv f := by
    apply ObjectProperty.hom_ext
    let f₀ : X.obj ⟶
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y.obj :=
      f.hom
    change (NonemptyAtlasAction.normalizationIso X).inv ≫
      restrictFromAction H (extendToAction H
        ((NonemptyAtlasAction.normalizationIso X).hom ≫ f₀)) = f₀
    rw [restrictFromAction_extendToAction, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

/-- Restriction precomposes the actual unit with the original normalization inverse. -/
theorem nonemptyHomEquiv_apply
    (p : (nonemptyCopiesFunctor H).obj X ⟶ Y) :
    (nonemptyHomEquiv H X Y p).hom =
      (NonemptyAtlasAction.normalizationIso X).inv ≫ restrictFromAction H p.hom := rfl

/-- Extension uses the forward normalization followed by the original supplied arrow. -/
theorem nonemptyHomEquiv_symm_apply
    (f : X ⟶ (NonemptyAtlasAction.restrict H.subtype).obj Y) :
    ((nonemptyHomEquiv H X Y).symm f).hom =
      extendToAction H ((NonemptyAtlasAction.normalizationIso X).hom ≫ f.hom) := rfl

variable {X X' Y Z}

/-- Naturality holds for all complete source arrows in the full subcategory. -/
theorem nonemptyHomEquiv_naturality_left (a : X' ⟶ X)
    (p : (nonemptyCopiesFunctor H).obj X ⟶ Y) :
    nonemptyHomEquiv H X' Y ((nonemptyCopiesFunctor H).map a ≫ p) =
      a ≫ nonemptyHomEquiv H X Y p := by
  apply ObjectProperty.hom_ext
  let p₀ : copiesAction H X.obj ⟶ Y.obj := p.hom
  change (NonemptyAtlasAction.normalizationIso X').inv ≫
      actionExtensionEquiv H (copiesEquivariantMap H a.hom ≫ p₀) =
    a.hom ≫ ((NonemptyAtlasAction.normalizationIso X).inv ≫
      actionExtensionEquiv H p₀)
  rw [actionExtensionEquiv_naturality_left, ← Category.assoc,
    ← NonemptyAtlasAction.normalizationIso_inv_naturality, Category.assoc]

/-- Naturality holds for all complete target arrows. -/
theorem nonemptyHomEquiv_naturality_right
    (p : (nonemptyCopiesFunctor H).obj X ⟶ Y) (q : Y ⟶ Z) :
    nonemptyHomEquiv H X Z (p ≫ q) = nonemptyHomEquiv H X Y p ≫
      (NonemptyAtlasAction.restrict H.subtype).map q := by
  apply ObjectProperty.hom_ext
  let p₀ : copiesAction H X.obj ⟶ Y.obj := p.hom
  change (NonemptyAtlasAction.normalizationIso X).inv ≫
      actionExtensionEquiv H (p₀ ≫ q.hom) =
    ((NonemptyAtlasAction.normalizationIso X).inv ≫ actionExtensionEquiv H p₀) ≫
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q.hom
  rw [actionExtensionEquiv_naturality_right, Category.assoc]

/-- The inverse correspondence is natural in the original source, without normalization. -/
theorem nonemptyHomEquiv_naturality_left_symm (a : X' ⟶ X)
    (f : X ⟶ (NonemptyAtlasAction.restrict H.subtype).obj Y) :
    (nonemptyHomEquiv H X' Y).symm (a ≫ f) =
      (nonemptyCopiesFunctor H).map a ≫ (nonemptyHomEquiv H X Y).symm f := by
  apply (nonemptyHomEquiv H X' Y).injective
  rw [nonemptyHomEquiv_naturality_left]
  simp only [Equiv.apply_symm_apply]

/-- Actual induction is left adjoint to restriction on these supplied atlas actions. -/
def nonemptyAdjunction : nonemptyCopiesFunctor (K := K) H ⊣
    NonemptyAtlasAction.restrict H.subtype :=
  Adjunction.mkOfHomEquiv
    { homEquiv := nonemptyHomEquiv H
      homEquiv_naturality_left_symm := nonemptyHomEquiv_naturality_left_symm H
      homEquiv_naturality_right := nonemptyHomEquiv_naturality_right H }

/-- The adjunction uses exactly the constructed original-source correspondence. -/
theorem nonemptyAdjunction_homEquiv :
    (nonemptyAdjunction (K := K) H).homEquiv = nonemptyHomEquiv H :=
  Adjunction.mkOfHomEquiv_homEquiv _

end Langlands.Analytic.AtlasInducedAction
