import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F : Presheaf S} {P U : Over S}

/-- A scheme representing a presheaf with closed diagonal is separated over the base. -/
theorem isSeparated_of_representableBy
    (e : F.RepresentableBy P) (hd : IsClosedImmersion (Limits.diag F)) :
    IsSeparated P.hom := by
  let e := (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F P) e
  let Y := schemeYoneda S
  have h₁ : IsPullback (𝟙 (Y.obj P)) (Y.map (Limits.diag P))
      (Limits.diag (Y.obj P)) (prodComparison Y P P) := by
    apply IsPullback.of_horiz_isIso
    constructor
    apply Limits.prod.hom_ext <;> simp [prodComparison, ← Functor.map_comp]
  have h₂ : IsPullback e.hom (Limits.diag (Y.obj P))
      (Limits.diag F) (Limits.prod.map e.hom e.hom) :=
    IsPullback.of_horiz_isIso ⟨(Limits.prod.diag_map e.hom).symm⟩
  have hc : _root_.AlgebraicGeometry.IsClosedImmersion (Limits.diag P).left := by
    apply hd.projection (prodComparison Y P P ≫ Limits.prod.map e.hom e.hom)
      e.hom (Limits.diag P)
    simpa using h₁.paste_horiz h₂
  have heq : (Limits.diag P).left ≫ (Over.prodLeftIsoPullback P P).hom =
      pullback.diagonal P.hom := by
    apply pullback.hom_ext <;> simp [← Over.comp_left]
  constructor
  rw [← heq]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _).mpr hc

/-- An atlas of a represented presheaf is induced by an actual surjective etale scheme map. -/
theorem exists_atlas_map_of_representableBy
    (e : F.RepresentableBy P) (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsEtale a) (hs : IsSurjective a) :
    ∃ b : U ⟶ P,
      (schemeYoneda S).map b ≫
        ((Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F P) e).hom = a ∧
      Etale b.left ∧ Surjective b.left := by
  let e := (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} F P) e
  obtain ⟨b, hb⟩ := (schemeYoneda S).map_surjective (a ≫ e.inv)
  have hb' : (schemeYoneda S).map b ≫ e.hom = a := by rw [hb]; simp
  have h : IsPullback (𝟙 ((schemeYoneda S).obj U))
      ((schemeYoneda S).map b) a e.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hb'.symm⟩
  exact ⟨b, hb', ha.projection e.hom (𝟙 _) b h,
    hs.projection e.hom (𝟙 _) b h⟩

/-- With source descent available, an atlas of local finite type transfers that property
    to any actual representing scheme. -/
theorem locallyOfFiniteType_of_representableBy_of_sourceDescent
    (hdesc : ∀ {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T),
      Surjective f → Flat f → LocallyOfFinitePresentation f →
        LocallyOfFiniteType (f ≫ g) → LocallyOfFiniteType g)
    (e : F.RepresentableBy P) (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsEtale a) (hs : IsSurjective a) (hU : LocallyOfFiniteType U.hom) :
    LocallyOfFiniteType P.hom := by
  obtain ⟨b, _, hbEtale, hbSurjective⟩ := exists_atlas_map_of_representableBy e a ha hs
  have : Etale b.left := hbEtale
  apply hdesc b.left P.hom hbSurjective inferInstance inferInstance
  simpa using hU

end Langlands.AlgebraicGeometry.AlgebraicSpace
