/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence

/-! # Horizontal coherence of the canonical additive Roos comparison

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, product-cone context, and the
agent-written coordinate calculation in the DAG proof
(blueprint: lem-pur-roos-comparison-horizontal-coherence).

The comparison is constructed directly by Mathlib's `mappingCocone.lift` on the fixed
`roosF` model, using the two mapped projections and the canonical product comparison.
No exactness or preservation of products is assumed for its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uA vA uB vB uD vD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasCountableProducts D]

private lemma productComparison_u (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosU X) ≫
        roosProductComparison F X =
      roosProductComparison F X ≫ roosU ((roosTowerAction F).obj X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    change FC.map (roosU X) ≫ piComparison FC _ =
      piComparison FC _ ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ FC.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Functor.map_comp]

private lemma cocone_snd_delta (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0 (CochainComplex.mappingCocone.snd (roosU X)) =
      -CochainComplex.HomComplex.Cochain.ofHom
        (CochainComplex.mappingCocone.fst (roosU X) ≫ roosU X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    open CochainComplex.HomComplex in
    dsimp only [CochainComplex.mappingCocone.snd]
    rw [Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega),
      CochainComplex.mappingCone.δ_snd]
    simp [CochainComplex.mappingCocone.fst]

private lemma cocone_fst_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.fst (roosU X)).f (p + 1) =
      (roosχ X p).hom ≫ biprod.snd := roosProj_f X p

private lemma cocone_snd_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) =
      (roosχ X p).hom ≫ biprod.fst := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' hq
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dite_eq_left hq]
    simp [roosχ, CochainComplex.mappingCocone.snd,
      CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
      hs p (p + 1) rfl, show Int.negOnePow 2 = 1 by rfl]

private lemma comparison_fst (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (roosProductComparison F X).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma comparison_snd (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫
        (roosProductComparison F X).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma productComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosPmap h) ≫
        roosProductComparison F Y =
      roosProductComparison F X ≫ roosPmap ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply Pi.hom_ext
    intro n
    change (_ ≫ roosProductComparison F Y) ≫ Pi.π (fun n : ℕ ↦
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Y.asFunctor.obj (op n))) n = _
    simp only [Category.assoc, roosProductComparison, piComparison_comp_π, roosPmap,
      Pi.map_π, ← Functor.map_comp]
    change _ = piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
      Pi.π (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (X.asFunctor.obj (op n))) n ≫ _
    rw [piComparison_comp_π_assoc, Functor.map_comp]
    rfl

private lemma roos_map_fst {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.fst =
      (roosχ X p).hom ≫ biprod.fst ≫ (roosPmap h).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

private lemma roos_map_snd {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.snd =
      (roosχ X p).hom ≫ biprod.snd ≫ (roosPmap h).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

/-- Naturality is equality of strict cochain maps.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 4. Postcompose with each product projection of each biproduct
coordinate. Both sides are the functor image of the same coordinate of the tower
map, by functoriality. Product and biproduct extensionality give equality. -/
theorem roosAdditiveComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
        roosAdditiveComparison F Y =
      roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
      roosAdditiveComparison F Y).f (p + 1) =
        (roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h)).f (p + 1)
    apply (cancel_mono (roosχ ((roosTowerAction F).obj Y) p).hom).1
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [comparison_fst F Y p, roos_map_fst ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_fst F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_fst]
      have hp := congrArg (fun f ↦ f.f p) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]
    · simp only [Category.assoc]
      erw [comparison_snd F Y p, roos_map_snd ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_snd F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_snd]
      have hp := congrArg (fun f ↦ f.f (p + 1)) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]

private lemma productComparison_horizontal
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (L : A ⥤ D) [L.Additive] (α : F ⋙ G ⟶ L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosProductComparison F X) ≫
        roosProductComparison G ((roosTowerAction F).obj X) ≫
        roosPmap ((NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosP X) ≫
        roosProductComparison L X := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let aX := (NatTrans.mapHomologicalComplex
      ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, roosPmap, Pi.map_π]
    change (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosProductComparison F X) ≫
      piComparison (G.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((roosTowerAction F).obj X).asFunctor.obj (op n))) n ≫ _ = _
    rw [piComparison_comp_π_assoc, ← Functor.map_comp_assoc]
    change (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (X.asFunctor.obj (op n))) n) ≫ _ = _
    rw [piComparison_comp_π]
    change _ = (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosP X) ≫
      piComparison (L.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (X.asFunctor.obj (op n))) n
    rw [piComparison_comp_π]
    ext p
    exact α.naturality ((Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p)

/-- Horizontal coherence for an arbitrary natural transformation GF → L.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 5. For either coordinate e and any product level, the left side
becomes alpha at that level followed by GF(e), while the right side is L(e)
following alpha at the Roos object. These agree by naturality of alpha at e.
Product and biproduct projections jointly detect equality of cochain maps.
Neither alpha nor either product comparison needs to be invertible. -/
theorem roosComparison_horizontal_coherence
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (L : A ⥤ D) [L.Additive] (α : F ⋙ G ⟶ L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosAdditiveComparison F X) ≫
        roosAdditiveComparison G ((roosTowerAction F).obj X) ≫
        roosF.map ((NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosF.obj X) ≫
        roosAdditiveComparison L X := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let aX := (NatTrans.mapHomologicalComplex
      ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (roosAdditiveComparison F X) ≫
        roosAdditiveComparison G ((roosTowerAction F).obj X) ≫ roosF.map aX).f (p + 1) =
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosF.obj X) ≫
        roosAdditiveComparison L X).f (p + 1)
    apply (cancel_mono (roosχ ((roosTowerAction L).obj X) p).hom).1
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [roos_map_fst aX p, reassoc_of% comparison_fst G ((roosTowerAction F).obj X) p,
        comparison_fst L X p]
      simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
      rw [← G.map_comp_assoc, comparison_fst, G.map_comp]
      have hp := congrArg (fun f ↦ f.f p) (productComparison_horizontal F G L α X)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f] at hp
      rw [Category.assoc, hp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ (roosProductComparison L X).f p)
          (α.naturality ((roosχ X p).hom ≫ biprod.fst))
    · simp only [Category.assoc]
      erw [roos_map_snd aX p, reassoc_of% comparison_snd G ((roosTowerAction F).obj X) p,
        comparison_snd L X p]
      simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
      rw [← G.map_comp_assoc, comparison_snd, G.map_comp]
      have hp := congrArg (fun f ↦ f.f (p + 1)) (productComparison_horizontal F G L α X)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f] at hp
      rw [Category.assoc, hp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ (roosProductComparison L X).f (p + 1))
          (α.naturality ((roosχ X p).hom ≫ biprod.snd))

/-- The identity comparison is the canonical identity identification.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 6. Every coordinate of the comparison for the identity functor is
unchanged. Joint monicity of the two sets of product projections proves equality. -/
theorem roosAdditiveComparison_id (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosAdditiveComparison (𝟭 A) X =
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app (roosF.obj X) ≫
        roosF.map ((Functor.mapHomologicalComplexIdIso (ℕᵒᵖ ⥤ A)
          (ComplexShape.up ℤ)).inv.app X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hp : roosProductComparison (𝟭 A) X = 𝟙 (roosP X) := by
      apply Pi.hom_ext
      intro n
      change piComparison ((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n = _
      erw [piComparison_comp_π]
      ext p
      change (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p =
        𝟙 _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p
      exact (Category.id_comp _).symm
    change roosAdditiveComparison (𝟭 A) X =
      𝟙 (roosF.obj X) ≫ roosF.map (𝟙 X)
    rw [roosF.map_id, Category.id_comp]
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change (roosAdditiveComparison (𝟭 A) X).f (p + 1) = 𝟙 _
    apply (cancel_mono (roosχ X p).hom).1
    apply biprod.hom_ext
    · erw [Category.assoc, comparison_fst (𝟭 A) X p]
      simp only [hp, HomologicalComplex.id_f, Functor.id_map, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, comparison_snd (𝟭 A) X p]
      simp only [hp, HomologicalComplex.id_f, Functor.id_map, Category.id_comp]
      exact Category.comp_id _

end CategoryTheory
