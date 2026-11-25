/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.CategoryTheory.SectionConjugateComparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Restriction of the coordinate comparison to the diagonal -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp derivedSquareUpperStarIso
  rightDerivedLowerStarComp
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensorIso
/-- Transport a coordinate restriction equation along its coefficient isomorphism. -/
theorem diagonalCoordinateTransport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G₁ G₂ : D ⥤ E) (H : E ⥤ D)
    (l₁ : G₁ ⋙ H ≅ 𝟭 D) (l₂ : G₂ ⋙ H ≅ 𝟭 D)
    (c : F ⋙ G₁ ⟶ F ⋙ G₂) (K : C) {M : D} (e : F.obj K ≅ M)
    (hc : H.map (c.app K) ≫ l₂.hom.app (F.obj K) = l₁.hom.app (F.obj K)) :
    H.map (G₁.map e.inv ≫ c.app K ≫ G₂.map e.hom) ≫ l₂.hom.app M =
      l₁.hom.app M := by
  have hn₂ := l₂.hom.naturality e.hom
  have hn₁ := l₁.hom.naturality e.inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn₁ hn₂
  simp only [H.map_comp, Category.assoc]
  rw [hn₂, reassoc_of% hc]
  rw [← Category.assoc, hn₁]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem conjugate_equality
    {C D : Type*} [Category C] [Category D] {I : Type*}
    (F : I → C ⥤ D) (G : I → D ⥤ C) (adj : ∀ i, F i ⊣ G i)
    {i j : I} (h : i = j) :
    (eqToIso (congrArg G h)).hom =
      conjugateEquiv (adj i) (adj j) (eqToIso (congrArg F h)).inv := by
  subst h
  simp

private theorem family_iso_inverse
    {C : Type*} [Category C] {I : Type*} (F : I → C) (M : C) (i : I)
    (c : ∀ (j : I), (j = i) → (F j ≅ M)) {j : I} (h : j = i) :
    (c i rfl).inv ≫ (eqToIso (congrArg F h.symm)).hom = (c j h).inv := by
  subst h
  simp

private theorem conjugate_inverse_of_hom
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {R S : D ⥤ C} (a : F ⊣ R) (b : G ⊣ S)
    (e : G ≅ F) (d : R ≅ S) (h : d.hom = conjugateEquiv a b e.hom) :
    d.inv = conjugateEquiv b a e.inv := by
  apply (cancel_mono d.hom).mp
  rw [Iso.inv_hom_id, h, conjugateEquiv_comp]
  simp

private theorem conjugate_triple
    {C D : Type*} [Category C] [Category D]
    {F₁ F₂ F₃ F₄ : C ⥤ D} {G₁ G₂ G₃ G₄ : D ⥤ C}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃) (a₄ : F₄ ⊣ G₄)
    (x : F₂ ⟶ F₁) (y : F₃ ⟶ F₂) (z : F₄ ⟶ F₃)
    (r : G₁ ⟶ G₂) (s : G₂ ⟶ G₃) (t : G₃ ⟶ G₄)
    (hr : r = conjugateEquiv a₁ a₂ x)
    (hs : s = conjugateEquiv a₂ a₃ y)
    (ht : t = conjugateEquiv a₃ a₄ z) :
    r ≫ s ≫ t = conjugateEquiv a₁ a₄ (z ≫ y ≫ x) := by
  rw [hr, hs, ht, conjugateEquiv_comp, conjugateEquiv_comp]
  simp only [Category.assoc]

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
/-- The conjugate section comparison, constructed for an arbitrary coefficient category. -/
def derivedSectionPushIso {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    (h : s ≫ p = 𝟙 X) :
    𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology B)) ≅
      (lowerStar B s).rightDerivedFunctor ⋙ (lowerStar B p).rightDerivedFunctor :=
  conjugateIsoEquiv Adjunction.id
    ((derivedUpperStarLowerStarAdjunction B p).comp
      (derivedUpperStarLowerStarAdjunction B s))
    (leftDerivedUpperStarCompSectionIso B s p h)

/-- The direct-image coordinate comparison, constructed before coefficient specialization. -/
def derivedDirectCoordinateIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar B (pullback.snd f f)).rightDerivedFunctor ⋙
        (lowerStar B f).rightDerivedFunctor ≅
      (lowerStar B (pullback.fst f f)).rightDerivedFunctor ⋙
        (lowerStar B f).rightDerivedFunctor :=
  rightDerivedLowerStarComp B (pullback.snd f f) f ≪≫
    eqToIso (congrArg (fun g ↦ (lowerStar B g).rightDerivedFunctor)
      (pullback.condition (f := f) (g := f)).symm) ≪≫
    (rightDerivedLowerStarComp B (pullback.fst f f) f).symm

/-- Tensor with the constant complex has its canonical right unitor. -/
def derivedSingleUnitorNatIso (X : Scheme.{u}) :
    derivedTensorRight B X ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology B).obj (𝟙_ B))) ≅
      𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology B)) :=
  (derivedTensorRightFunctor B X).mapIso (singleFunctorObjUnitIso B X) ≪≫
    ordinaryDerivedTensorRightUnitorNatIso B X

/-- Components of the constant-complex unitor use the cached tensor bifunctor. -/
theorem derivedSingleUnitorNatIso_hom_app (X : Scheme.{u})
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (derivedSingleUnitorNatIso B X).hom.app M =
      ((derivedTensor B X).obj M).map (singleFunctorObjUnitIso B X).hom ≫
        (derivedTensorRightUnitor B X M).hom := by
  rfl

/-- Cancel constant-unit transport before applying the derived right unitor. -/
theorem derivedSingleUnitorNatIso_cancel (X : Scheme.{u})
    (M V : DerivedCategory (Sheaf X.smallEtaleTopology B)) (t : V ⟶ 𝟙_ _) :
    ((derivedTensor B X).obj M).map (t ≫ (singleFunctorObjUnitIso B X).inv) ≫
        (derivedSingleUnitorNatIso B X).hom.app M =
      ((derivedTensor B X).obj M).map t ≫ (derivedTensorRightUnitor B X M).hom := by
  rw [derivedSingleUnitorNatIso_hom_app, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc]

theorem rightDerivedLowerStarComp_hom_eq_conjugate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightDerivedLowerStarComp B f g).hom =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction B g).comp
          (derivedUpperStarLowerStarAdjunction B f))
        (derivedUpperStarLowerStarAdjunction B (f ≫ g))
        (leftDerivedUpperStarComp B f g (f ≫ g) rfl).hom := by
  rw [conjugateEquiv_leftDerivedUpperStarComp_hom]
  simp only [rightDerivedLowerStarComp, conjugateIsoEquiv_apply_inv, Iso.symm_hom,
    Iso.symm_inv]
theorem diagonalSection_coordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (upperStar B (pullback.diagonal f)).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso B
          (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom.app K) ≫
      (leftDerivedUpperStarCompSectionIso B (pullback.diagonal f) (pullback.snd f f)
        (pullback.diagonal_snd f)).hom.app ((upperStar B f).leftDerivedFunctor.obj K) =
    (leftDerivedUpperStarCompSectionIso B (pullback.diagonal f) (pullback.fst f f)
      (pullback.diagonal_fst f)).hom.app ((upperStar B f).leftDerivedFunctor.obj K) := by
  have h₁ := leftDerivedUpperStarComp_assoc'_app B (pullback.diagonal f)
    (pullback.fst f f) f (𝟙 X) (pullback.snd f f ≫ f) f
    (pullback.diagonal_fst f).symm pullback.condition.symm
    (Category.id_comp f).symm K
  have h₂ := leftDerivedUpperStarComp_assoc'_app B (pullback.diagonal f)
    (pullback.snd f f) f (𝟙 X) (pullback.snd f f ≫ f) f
    (pullback.diagonal_snd f).symm rfl (Category.id_comp f).symm K
  apply (cancel_epi
    ((leftDerivedUpperStarComp B (pullback.diagonal f) (pullback.snd f f ≫ f) f
        (by simp [← Category.assoc])).hom.app K ≫
      (upperStar B (pullback.diagonal f)).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp B (pullback.fst f f) f
          (pullback.snd f f ≫ f) pullback.condition.symm).hom.app K))).mp
  simp only [derivedSquareUpperStarIso, leftDerivedUpperStarCompSectionIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rw [← Category.assoc, h₂, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The direct-image coordinate comparison is conjugate to the inverse-image square. -/
theorem diagonalSection_directComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (rightDerivedLowerStarComp B (pullback.snd f f) f ≪≫
      eqToIso (congrArg (fun g ↦ (lowerStar B g).rightDerivedFunctor)
        (pullback.condition (f := f) (g := f)).symm) ≪≫
      (rightDerivedLowerStarComp B (pullback.fst f f) f).symm).hom =
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction B f).comp
        (derivedUpperStarLowerStarAdjunction B (pullback.snd f f)))
      ((derivedUpperStarLowerStarAdjunction B f).comp
        (derivedUpperStarLowerStarAdjunction B (pullback.fst f f)))
      (derivedSquareUpperStarIso B
        (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom := by
  let p₁ := pullback.fst f f
  let p₂ := pullback.snd f f
  have hcongr {g g' : pullback f f ⟶ Y} (h : g = g') :
      (eqToIso (congrArg (fun g ↦ (lowerStar B g).rightDerivedFunctor) h)).hom =
        conjugateEquiv (derivedUpperStarLowerStarAdjunction B g)
          (derivedUpperStarLowerStarAdjunction B g')
          (eqToIso (congrArg (fun g ↦ (upperStar B g).leftDerivedFunctor) h)).inv := by
    exact conjugate_equality
      (fun g ↦ (upperStar B g).leftDerivedFunctor)
      (fun g ↦ (lowerStar B g).rightDerivedFunctor)
      (fun g ↦ derivedUpperStarLowerStarAdjunction B g) h
  have hinv : (rightDerivedLowerStarComp B p₁ f).inv =
      conjugateEquiv (derivedUpperStarLowerStarAdjunction B (p₁ ≫ f))
        ((derivedUpperStarLowerStarAdjunction B f).comp
          (derivedUpperStarLowerStarAdjunction B p₁))
        (leftDerivedUpperStarComp B p₁ f).inv := by
    exact conjugate_inverse_of_hom
      ((derivedUpperStarLowerStarAdjunction B f).comp
        (derivedUpperStarLowerStarAdjunction B p₁))
      (derivedUpperStarLowerStarAdjunction B (p₁ ≫ f))
      (leftDerivedUpperStarComp B p₁ f) (rightDerivedLowerStarComp B p₁ f)
      (rightDerivedLowerStarComp_hom_eq_conjugate B p₁ f)
  have hpaste := conjugate_triple
    ((derivedUpperStarLowerStarAdjunction B f).comp
      (derivedUpperStarLowerStarAdjunction B p₂))
    (derivedUpperStarLowerStarAdjunction B (p₂ ≫ f))
    (derivedUpperStarLowerStarAdjunction B (p₁ ≫ f))
    ((derivedUpperStarLowerStarAdjunction B f).comp
      (derivedUpperStarLowerStarAdjunction B p₁))
    (leftDerivedUpperStarComp B p₂ f).hom
    (eqToIso (congrArg (fun g ↦ (upperStar B g).leftDerivedFunctor)
      (pullback.condition (f := f) (g := f)).symm)).inv
    (leftDerivedUpperStarComp B p₁ f).inv
    (rightDerivedLowerStarComp B p₂ f).hom
    (eqToIso (congrArg (fun g ↦ (lowerStar B g).rightDerivedFunctor)
      (pullback.condition (f := f) (g := f)).symm)).hom
    (rightDerivedLowerStarComp B p₁ f).inv
    (rightDerivedLowerStarComp_hom_eq_conjugate B p₂ f)
    (hcongr pullback.condition.symm) hinv
  refine hpaste.trans ?_
  apply congrArg (conjugateEquiv _ _)
  have hh {g : pullback f f ⟶ Y} (e : g = p₁ ≫ f) :
      (leftDerivedUpperStarComp B p₁ f).inv ≫
          (eqToIso (congrArg (fun g ↦ (upperStar B g).leftDerivedFunctor) e.symm)).hom =
        (leftDerivedUpperStarComp B p₁ f g e).inv := by
    exact family_iso_inverse
      (fun g ↦ (upperStar B g).leftDerivedFunctor)
      ((upperStar B f).leftDerivedFunctor ⋙ (upperStar B p₁).leftDerivedFunctor)
      (p₁ ≫ f) (fun g h ↦ leftDerivedUpperStarComp B p₁ f g h) e
  simpa only [eqToIso.inv, eqToIso.hom, derivedSquareUpperStarIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    congrArg (fun z ↦ z ≫ (leftDerivedUpperStarComp B p₂ f).hom)
      (hh pullback.condition.symm)

/-- The pushforward comparison preserves the diagonal section identification. -/
theorem diagonalSection_push_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let a₁ := derivedSectionPushIso B (pullback.diagonal f) (pullback.fst f f)
      (pullback.diagonal_fst f)
    let a₂ := derivedSectionPushIso B (pullback.diagonal f) (pullback.snd f f)
      (pullback.diagonal_snd f)
    let d := (derivedDirectCoordinateIso B f).hom
    Functor.whiskerRight a₂.hom (lowerStar B f).rightDerivedFunctor ≫
        Functor.whiskerLeft (lowerStar B (pullback.diagonal f)).rightDerivedFunctor d =
      Functor.whiskerRight a₁.hom (lowerStar B f).rightDerivedFunctor := by
  intro a₁ a₂ d
  dsimp only [d, derivedDirectCoordinateIso]
  rw [diagonalSection_directComparison]
  dsimp only [a₁, a₂, derivedSectionPushIso]
  exact Adjunction.conjugate_section_comparison
    (derivedUpperStarLowerStarAdjunction B f)
    (derivedUpperStarLowerStarAdjunction B (pullback.fst f f))
    (derivedUpperStarLowerStarAdjunction B (pullback.snd f f))
    (derivedUpperStarLowerStarAdjunction B (pullback.diagonal f))
    (leftDerivedUpperStarCompSectionIso B (pullback.diagonal f)
      (pullback.fst f f) (pullback.diagonal_fst f))
    (leftDerivedUpperStarCompSectionIso B (pullback.diagonal f)
      (pullback.snd f f) (pullback.diagonal_snd f))
    (derivedSquareUpperStarIso B
      (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom
    (by ext K; exact diagonalSection_coordinate B f K)

/-- The component form of section compatibility, before coefficient specialization. -/
theorem diagonalSection_push_comparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (lowerStar B f).rightDerivedFunctor.map
        ((derivedSectionPushIso B (pullback.diagonal f) (pullback.snd f f)
          (pullback.diagonal_snd f)).hom.app K) ≫
      (derivedDirectCoordinateIso B f).hom.app
        ((lowerStar B (pullback.diagonal f)).rightDerivedFunctor.obj K) =
    (lowerStar B f).rightDerivedFunctor.map
      ((derivedSectionPushIso B (pullback.diagonal f) (pullback.fst f f)
        (pullback.diagonal_fst f)).hom.app K) := by
  exact NatTrans.congr_app (diagonalSection_push_comparison B f) K

/-- Naturality of section compatibility at an arbitrary morphism out of the diagonal. -/
theorem diagonalSection_push_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B))
    {V : DerivedCategory (Sheaf (pullback f f).smallEtaleTopology B)}
    (d : (lowerStar B (pullback.diagonal f)).rightDerivedFunctor.obj K ⟶ V) :
    (lowerStar B f).rightDerivedFunctor.map
        ((derivedSectionPushIso B (pullback.diagonal f) (pullback.snd f f)
          (pullback.diagonal_snd f)).hom.app K ≫
          (lowerStar B (pullback.snd f f)).rightDerivedFunctor.map d) ≫
      (derivedDirectCoordinateIso B f).hom.app V =
    (lowerStar B f).rightDerivedFunctor.map
      ((derivedSectionPushIso B (pullback.diagonal f) (pullback.fst f f)
        (pullback.diagonal_fst f)).hom.app K ≫
        (lowerStar B (pullback.fst f f)).rightDerivedFunctor.map d) := by
  exact Adjunction.section_comparison_naturality
    (lowerStar B (pullback.diagonal f)).rightDerivedFunctor
    (lowerStar B (pullback.snd f f)).rightDerivedFunctor
    (lowerStar B (pullback.fst f f)).rightDerivedFunctor
    (lowerStar B f).rightDerivedFunctor
    (derivedSectionPushIso B (pullback.diagonal f) (pullback.snd f f)
      (pullback.diagonal_snd f)).hom
    (derivedSectionPushIso B (pullback.diagonal f) (pullback.fst f f)
      (pullback.diagonal_fst f)).hom
    (derivedDirectCoordinateIso B f).hom
    (fun J ↦ diagonalSection_push_comparison_app B f J) K d

end AlgebraicGeometry.Etale
