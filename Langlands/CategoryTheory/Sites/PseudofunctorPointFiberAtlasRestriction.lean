import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber

/-! # Point fibres after restricting the atlas object along a monomorphism -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {U V T : C} (i : V ⟶ U) (ξ : F.obj (.mk (op U)))
  (η : F.obj (.mk (op T)))

/-- Compare pullback from the original atlas with iterated pullback. -/
def atlasComparison {Z : C} (a : Z ⟶ V) :
    (F.map (a ≫ i).op.toLoc).toFunctor.obj ξ ≅
      (F.map a.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj ξ) :=
  (Cat.Hom.toNatIso (F.mapComp' i.op.toLoc a.op.toLoc (a ≫ i).op.toLoc
    (by simp))).app ξ

/-- A restricted-atlas point retains its isomorphism and composes its base map. -/
def mapPoints (Z : Over T) :
    Points F ((F.map i.op.toLoc).toFunctor.obj ξ) η Z → Points F ξ η Z :=
  fun x ↦ ⟨x.1 ≫ i, atlasComparison F i ξ x.1 ≪≫ x.2⟩

/-- The composition comparison commutes with coherent restriction. -/
lemma atlasComparison_pullIso {Z Z' : C} {a : Z ⟶ V} {p : Z ⟶ T}
    (e : (F.map a.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj ξ) ≅
      (F.map p.op.toLoc).toFunctor.obj η)
    (q : Z' ⟶ Z) (qa : Z' ⟶ V) (qp : Z' ⟶ T)
    (ha : q ≫ a = qa) (hp : q ≫ p = qp) :
    atlasComparison F i ξ qa ≪≫ pullIso e q qa qp ha hp =
      pullIso (atlasComparison F i ξ a ≪≫ e) q (qa ≫ i) qp
        (by rw [← ha, Category.assoc]) hp := by
  apply Iso.ext
  simp only [atlasComparison, pullIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso,
    Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    i.op.toLoc a.op.toLoc q.op.toLoc (a ≫ i).op.toLoc qa.op.toLoc
    (qa ≫ i).op.toLoc (by simp) (by simp [← ha]) (by simp [← ha])]

/-- The actual point map is natural on every object and map of the slice. -/
lemma mapPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : Points F ((F.map i.op.toLoc).toFunctor.obj ξ) η Z) :
    mapPoints F i ξ η Z' (restrict F _ η q x) =
      restrict F ξ η q (mapPoints F i ξ η Z x) := by
  rcases x with ⟨a, e⟩
  dsimp only [mapPoints, restrict]
  have h (b : Z'.left ⟶ U) (hb : (q.left ≫ a) ≫ i = b) :
      (⟨(q.left ≫ a) ≫ i,
        atlasComparison F i ξ (q.left ≫ a) ≪≫
          pullIso e q.left (q.left ≫ a) Z'.hom rfl q.w⟩ : Points F ξ η Z') =
      ⟨b, pullIso (atlasComparison F i ξ a ≪≫ e) q.left b Z'.hom
        (by rw [← hb, Category.assoc]) q.w⟩ := by
    subst b
    exact congrArg (fun e ↦ (⟨(q.left ≫ a) ≫ i, e⟩ : Points F ξ η Z'))
      (atlasComparison_pullIso F i ξ η e q.left (q.left ≫ a) Z'.hom rfl q.w)
  exact h _ (Category.assoc _ _ _)

/-- Postcomposition on atlas maps defines a natural transformation of point fibres. -/
def presheafMap :
    presheaf F ((F.map i.op.toLoc).toFunctor.obj ξ) η ⟶ presheaf F ξ η where
  app Z := ↾(mapPoints F i ξ η Z.unop)
  naturality {_ _} q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict F i ξ η q.unop x

/-- Monicity makes the actual point map injective, including its isomorphism data. -/
lemma mapPoints_injective [Mono i] (Z : Over T) :
    Function.Injective (mapPoints F i ξ η Z) := by
  rintro ⟨a, e⟩ ⟨b, e'⟩ h
  have hab : a = b := (cancel_mono i).mp (congrArg Sigma.fst h)
  subst b
  have he : atlasComparison F i ξ a ≪≫ e = atlasComparison F i ξ a ≪≫ e' := by
    simpa only [mapPoints, Sigma.mk.injEq, heq_eq_eq, true_and] using h
  have he' : e = e' := by
    apply Iso.ext
    exact (cancel_epi (atlasComparison F i ξ a).hom).mp (congrArg Iso.hom he)
  subst e'
  rfl

/-- Factorization of all original points makes the actual point map surjective. -/
lemma mapPoints_surjective (Z : Over T)
    (hlift : ∀ x : Points F ξ η Z, ∃ a : Z.left ⟶ V, a ≫ i = x.1) :
    Function.Surjective (mapPoints F i ξ η Z) := by
  rintro ⟨b, e⟩
  obtain ⟨a, ha⟩ := hlift ⟨b, e⟩
  dsimp only at ha
  subst b
  refine ⟨⟨a, (atlasComparison F i ξ a).symm ≪≫ e⟩, ?_⟩
  simp [mapPoints]

/-- Restricting the atlas gives the same actual points whenever all maps factor. -/
def pointsEquiv [Mono i] (Z : Over T)
    (hlift : ∀ x : Points F ξ η Z, ∃ a : Z.left ⟶ V, a ≫ i = x.1) :
    Points F ((F.map i.op.toLoc).toFunctor.obj ξ) η Z ≃ Points F ξ η Z :=
  Equiv.ofBijective (mapPoints F i ξ η Z)
    ⟨mapPoints_injective F i ξ η Z, mapPoints_surjective F i ξ η Z hlift⟩

/-- The equivalence keeps the explicit forward map on actual points. -/
lemma pointsEquiv_apply [Mono i] (Z : Over T)
    (hlift : ∀ x : Points F ξ η Z, ∃ a : Z.left ⟶ V, a ≫ i = x.1)
    (x : Points F ((F.map i.op.toLoc).toFunctor.obj ξ) η Z) :
    pointsEquiv F i ξ η Z hlift x = mapPoints F i ξ η Z x := rfl

/-- The entire point fibres agree naturally on the full slice. -/
def presheafIso [Mono i]
    (hlift : ∀ (Z : Over T) (x : Points F ξ η Z),
      ∃ a : Z.left ⟶ V, a ≫ i = x.1) :
    presheaf F ((F.map i.op.toLoc).toFunctor.obj ξ) η ≅ presheaf F ξ η :=
  NatIso.ofComponents (fun Z ↦ (pointsEquiv F i ξ η Z.unop (hlift Z.unop)).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict F i ξ η q.unop x)

end Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction
