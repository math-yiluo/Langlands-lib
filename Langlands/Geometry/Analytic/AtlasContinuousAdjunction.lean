import Langlands.Geometry.Analytic.AtlasContinuousQuotient
import Langlands.Geometry.Analytic.AtlasInducedQuotientUniversal
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Balanced-quotient induction adjunction for jointly continuous atlas actions -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

attribute [local instance] sourceContinuousSMul

variable (X X' : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H)
  (Y Z : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K G)

/-- Expose the actual bounded normalization isomorphism with the original source type. -/
def pointContinuousSourceNormalizationIso : normalizedAction H X.obj ≅ X.obj :=
  NonemptyAtlasAction.normalizationIso
    (PointContinuousNonemptyAtlasAction.toNonempty.obj X)

omit [IsTopologicalGroup G] in
/-- The original typed normalization inverse commutes with every complete source arrow. -/
theorem pointContinuousSourceNormalizationIso_inv_naturality
    {X X' : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H}
    (a : X' ⟶ X) :
    a.hom ≫ (pointContinuousSourceNormalizationIso H X).inv =
      (pointContinuousSourceNormalizationIso H X').inv ≫
        (AffinoidAtlasPresentation.nonemptyActionFunctor H).map a.hom :=
  NonemptyAtlasAction.normalizationIso_inv_naturality
    (PointContinuousNonemptyAtlasAction.toNonempty.map a)

/-- The quotient correspondence on the original source, using its bounded normalization iso. -/
def pointContinuousHomEquiv :
    ((pointContinuousQuotientFunctor H hH).obj X ⟶ Y) ≃
      (X ⟶ (pointContinuousRestriction H).obj Y) where
  toFun p := ObjectProperty.homMk
    ((pointContinuousSourceNormalizationIso H X).inv ≫
        quotientActionExtensionEquiv H hH (X := X.obj) p.hom)
  invFun f := ObjectProperty.homMk
    (quotientExtendToAction H hH (X := X.obj)
      ((pointContinuousSourceNormalizationIso H X).hom ≫ f.hom))
  left_inv p := by
    apply ObjectProperty.hom_ext
    let p₀ : action H X.obj hH ⟶ Y.obj := p.hom
    change quotientExtendToAction H hH (X := X.obj)
      ((pointContinuousSourceNormalizationIso H X).hom ≫
      ((pointContinuousSourceNormalizationIso H X).inv ≫
          quotientRestrictFromAction H hH (X := X.obj) p₀)) = p₀
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      quotientExtendToAction_quotientRestrictFromAction]
  right_inv f := by
    apply ObjectProperty.hom_ext
    let f₀ : X.obj ⟶
        (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K)
          H.subtype).obj Y.obj := f.hom
    change (pointContinuousSourceNormalizationIso H X).inv ≫
        quotientRestrictFromAction H hH (X := X.obj) (quotientExtendToAction H hH (X := X.obj)
          ((pointContinuousSourceNormalizationIso H X).hom ≫ f₀)) = f₀
    rw [quotientRestrictFromAction_quotientExtendToAction, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

/-- The forward map composes the actual quotient unit with the normalization inverse. -/
theorem pointContinuousHomEquiv_apply
    (p : (pointContinuousQuotientFunctor H hH).obj X ⟶ Y) :
    (pointContinuousHomEquiv H hH X Y p).hom =
      (pointContinuousSourceNormalizationIso H X).inv ≫
          quotientRestrictFromAction H hH (X := X.obj) p.hom := rfl

/-- Extension uses the original full arrow after the constructed forward normalization. -/
theorem pointContinuousHomEquiv_symm_apply
    (f : X ⟶ (pointContinuousRestriction H).obj Y) :
    ((pointContinuousHomEquiv H hH X Y).symm f).hom =
      quotientExtendToAction H hH (X := X.obj)
        ((pointContinuousSourceNormalizationIso H X).hom ≫ f.hom) := rfl

variable {X X' Y Z}

/-- Source naturality retains the full equivariant bounded source arrow. -/
theorem pointContinuousHomEquiv_naturality_left (a : X' ⟶ X)
    (p : (pointContinuousQuotientFunctor H hH).obj X ⟶ Y) :
    pointContinuousHomEquiv H hH X' Y
        ((pointContinuousQuotientFunctor H hH).map a ≫ p) =
      a ≫ pointContinuousHomEquiv H hH X Y p := by
  apply ObjectProperty.hom_ext
  let p₀ : action H X.obj hH ⟶ Y.obj := p.hom
  change (pointContinuousSourceNormalizationIso H X').inv ≫
      quotientActionExtensionEquiv H hH (X := X'.obj) (quotientEquivariantMap H hH a.hom ≫ p₀) =
    a.hom ≫ ((pointContinuousSourceNormalizationIso H X).inv ≫
        quotientActionExtensionEquiv H hH (X := X.obj) p₀)
  rw [quotientActionExtensionEquiv_naturality_left, ← Category.assoc,
    ← pointContinuousSourceNormalizationIso_inv_naturality H a, Category.assoc]

/-- Target naturality retains the full equivariant bounded target arrow. -/
theorem pointContinuousHomEquiv_naturality_right
    (p : (pointContinuousQuotientFunctor H hH).obj X ⟶ Y) (q : Y ⟶ Z) :
    pointContinuousHomEquiv H hH X Z (p ≫ q) =
      pointContinuousHomEquiv H hH X Y p ≫ (pointContinuousRestriction H).map q := by
  apply ObjectProperty.hom_ext
  let p₀ : action H X.obj hH ⟶ Y.obj := p.hom
  change (pointContinuousSourceNormalizationIso H X).inv ≫
      quotientActionExtensionEquiv H hH (X := X.obj) (p₀ ≫ q.hom) =
    ((pointContinuousSourceNormalizationIso H X).inv ≫
        quotientActionExtensionEquiv H hH (X := X.obj) p₀) ≫
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).map q.hom
  rw [quotientActionExtensionEquiv_naturality_right, Category.assoc]

/-- The inverse correspondence is natural in the original continuous source category. -/
theorem pointContinuousHomEquiv_naturality_left_symm (a : X' ⟶ X)
    (f : X ⟶ (pointContinuousRestriction H).obj Y) :
    (pointContinuousHomEquiv H hH X' Y).symm (a ≫ f) =
      (pointContinuousQuotientFunctor H hH).map a ≫
        (pointContinuousHomEquiv H hH X Y).symm f := by
  apply (pointContinuousHomEquiv H hH X' Y).injective
  rw [pointContinuousHomEquiv_naturality_left]
  simp only [Equiv.apply_symm_apply]

/-- Actual balanced-quotient induction is left adjoint to continuous subgroup restriction. -/
def pointContinuousAdjunction : pointContinuousQuotientFunctor (K := K) H hH ⊣
    pointContinuousRestriction H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pointContinuousHomEquiv H hH
      homEquiv_naturality_left_symm := pointContinuousHomEquiv_naturality_left_symm H hH
      homEquiv_naturality_right := pointContinuousHomEquiv_naturality_right H hH }

/-- The adjunction's Hom equivalence is exactly the constructed original-source map. -/
theorem pointContinuousAdjunction_homEquiv :
    (pointContinuousAdjunction (K := K) H hH).homEquiv =
      pointContinuousHomEquiv H hH :=
  Adjunction.mkOfHomEquiv_homEquiv _

end Langlands.Analytic.AtlasInducedAction
