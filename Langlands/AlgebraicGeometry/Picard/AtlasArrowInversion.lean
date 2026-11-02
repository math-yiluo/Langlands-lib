import Langlands.AlgebraicGeometry.Picard.AtlasArrowScheme

/-! # Inverting actual Picard arrows -/

universe u v v' w w'

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type w} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', w'}}

/-- Coherent pullback commutes with inversion of an actual isomorphism. -/
lemma pullIso_symm {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullIso e.symm g gf₂ gf₁ hgf₂ hgf₁ =
      (pullIso e g gf₁ gf₂ hgf₁ hgf₂).symm := by
  simp only [pullIso, Iso.trans_symm, Functor.mapIso_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Invert the full arrows of an arbitrary category-valued pseudofunctor. -/
def totalArrowInverse (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', w'})
    {U : C} (ξ : F.obj (.mk (op U))) :
    (presheaf F ξ ξ).overTotal ⟶ (presheaf F ξ ξ).overTotal where
  app _ := ↾fun x ↦ ⟨x.2.1, x.1, x.2.2.symm⟩
  naturality {T V} g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨g.unop ≫ x.2.1, g.unop ≫ x.1,
        (pullIso x.2.2 g.unop (g.unop ≫ x.2.1) (g.unop ≫ x.1) rfl rfl).symm⟩ :
          (presheaf F ξ ξ).OverTotal V.unop) =
      ⟨g.unop ≫ x.2.1, g.unop ≫ x.1,
        pullIso x.2.2.symm g.unop (g.unop ≫ x.1) (g.unop ≫ x.2.1) rfl rfl⟩
    exact congrArg
      (fun j ↦ (⟨g.unop ≫ x.2.1, g.unop ≫ x.1, j⟩ :
        (presheaf F ξ ξ).OverTotal V.unop))
      (pullIso_symm x.2.2 g.unop (g.unop ≫ x.2.1) (g.unop ≫ x.1) rfl rfl).symm

end Langlands.CategoryTheory.PseudofunctorPointFiber

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- Reverse the actual endpoint maps and invert the retained bundle isomorphism. -/
def atlasArrowInverse : atlasArrowPresheaf f L ⟶ atlasArrowPresheaf f L :=
  Functor.whiskerRight (totalArrowInverse (relative f) (Core.mk L)) uliftFunctor.{u + 1}

/-- Actual inversion is an involution on the entire arrow presheaf. -/
lemma atlasArrowInverse_involutive :
    atlasArrowInverse f L ≫ atlasArrowInverse f L = 𝟙 _ := by
  ext T x
  rfl

/-- The actual arrow presheaf has a natural inversion isomorphism. -/
def atlasArrowInverseIso : atlasArrowPresheaf f L ≅ atlasArrowPresheaf f L where
  hom := atlasArrowInverse f L
  inv := atlasArrowInverse f L
  hom_inv_id := atlasArrowInverse_involutive f L
  inv_hom_id := atlasArrowInverse_involutive f L

/-- Inversion exchanges the two complete family projections. -/
lemma atlasArrowInverse_snd :
    atlasArrowInverse f L ≫ atlasArrowSnd f L = atlasArrowFst f L := rfl

/-- A full Picard arrow scheme has two smooth surjective endpoints. -/
lemma exists_atlasArrowScheme (hL : IsSmoothSurjectivePresentation f L) :
    ∃ (A : Over S) (s t : A ⟶ U)
      (e : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L),
      e.hom ≫ atlasArrowFst f L = (AlgebraicSpace.schemeYoneda S).map s ∧
        e.hom ≫ atlasArrowSnd f L = (AlgebraicSpace.schemeYoneda S).map t ∧
        Smooth s.left ∧ Surjective s.left ∧ Smooth t.left ∧ Surjective t.left := by
  obtain ⟨A, t, e, ht, hsm, hsurj⟩ := exists_atlasArrowScheme_snd f L hL
  let i : A ≅ A := (AlgebraicSpace.schemeYoneda S).preimageIso
    (e ≪≫ atlasArrowInverseIso f L ≪≫ e.symm)
  let s : A ⟶ U := i.hom ≫ t
  have hi : (AlgebraicSpace.schemeYoneda S).map i.hom =
      e.hom ≫ atlasArrowInverse f L ≫ e.inv := by
    simp [i, Functor.preimageIso, atlasArrowInverseIso]
  have hs : e.hom ≫ atlasArrowFst f L = (AlgebraicSpace.schemeYoneda S).map s := by
    dsimp only [s]
    rw [Functor.map_comp, hi, ← ht]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [atlasArrowInverse_snd]
  let : Smooth t.left := hsm
  let : Surjective t.left := hsurj
  have : IsIso i.hom.left := (Over.forget S).map_isIso i.hom
  refine ⟨A, s, t, e, hs, ht, ?_, ?_, hsm, hsurj⟩
  · change Smooth (i.hom.left ≫ t.left)
    infer_instance
  · change Surjective (i.hom.left ≫ t.left)
    infer_instance

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
