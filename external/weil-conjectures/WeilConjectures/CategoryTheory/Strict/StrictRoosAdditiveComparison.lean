/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Additive comparison for the strict Roos cone

Source: Stacks 08TC and 0H9K; finite-product/cone portion of proof step 7 of
`lem-pur-compact-support-roos-cofinality`.
-/

@[expose] public section

set_option autoImplicit false

universe u v vA vB

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory

variable {A : Type u} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
open HomologicalComplex
open StrictTowerArithmetic
/-- The shifted cone map induced by a commuting square of Roos differentials.
Source: Stacks 08TC and 0H9K
(blueprint: lem-pur-roos-additive-comparison). -/
noncomputable def strictRoosMapOfSquare {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (h : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b) :
    strictRoosComplex X ⟶ strictRoosComplex Y :=
  (homotopyCofiber.mapArrowHom _ _ (fun j : ℤ ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
    (Arrow.homMk a b h))⟦(-1 : ℤ)⟧'
set_option backward.isDefEq.respectTransparency false in
omit [HasCountableProducts A] in
private theorem roosConeMap_coordinates {P Q P' Q' : CochainComplex A ℤ}
    (φ : P ⟶ Q) (ψ : P' ⟶ Q') (α : Arrow.mk φ ⟶ Arrow.mk ψ) (p : ℤ) :
    (homotopyCofiber.mapArrowHom φ ψ
      (fun j : ℤ ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
      α).f p ≫
      (homotopyCofiber.XIsoBiprod ψ p (p + 1) rfl).hom ≫
      (biprod.braiding _ _).hom =
    (homotopyCofiber.XIsoBiprod φ p (p + 1) rfl).hom ≫
      (biprod.braiding _ _).hom ≫ biprod.map (α.right.f p) (α.left.f (p + 1)) := by
  apply (cancel_epi (homotopyCofiber.XIsoBiprod φ p (p + 1) rfl).inv).mp
  apply biprod.hom_ext'
  · simp only [homotopyCofiber_X, biprod.braiding_hom,
      homotopyCofiber.inl_XIsoBiprod_inv_assoc, Arrow.mk_right,
      Arrow.mk_left, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext <;>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
        homotopyCofiber.inrCompHomotopy_hom]
  · simp only [homotopyCofiber_X, biprod.braiding_hom,
      homotopyCofiber.inr_XIsoBiprod_inv_assoc, Arrow.mk_right,
      Arrow.mk_left, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext <;>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f,
        homotopyCofiber.inrCompHomotopy_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The induced shifted cone map has its prescribed two coordinates.
Source: Stacks 08TC and 0H9K
(blueprint: lem-pur-roos-additive-comparison). -/
theorem strictRoosMapOfSquare_coordinates {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (h : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b) (p : ℤ) :
    (strictRoosMapOfSquare a b h).f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫ biprod.map (b.f p) (a.f (p + 1)) := by
  dsimp only [strictRoosMapOfSquare, strictRoosCoordinates, Iso.trans_hom,
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  rw [XIsoOfEq_hom_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  exact roosConeMap_coordinates _ _ _ p

/-- A strict tower morphism commutes with the Roos differential.
Source: Stacks 08TC and 0H9K
(blueprint: lem-pur-roos-additive-comparison). -/
theorem strictRoosProductMap_comm {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    strictRoosProductMap f ≫ strictRoosEndomorphism Y =
      strictRoosEndomorphism X ≫ strictRoosProductMap f := by
  apply towerTransitionEndomorphism_natural_backward
  intro n
  exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Finite telescoping makes selection and block a square of Roos differentials.
Source: Stacks 08TC and 0H9K
(blueprint: lem-pur-roos-additive-comparison). -/
theorem strictRoosBlock_comm (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    selection e X.asFunctor ≫
        strictRoosEndomorphism ((complexRestriction A e).obj X) =
      strictRoosEndomorphism X ≫ block e X.asFunctor := by
  change selection e X.asFunctor ≫ towerTransitionEndomorphism
    (fun n ↦ X.asFunctor.map ((index e).map (homOfLE (Nat.le_succ n)).op)) =
    strictRoosEndomorphism X ≫ block e X.asFunctor
  apply Pi.hom_ext
  intro n
  simp only [selection, block, strictRoosEndomorphism, towerTransitionEndomorphism,
    towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.id_comp, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
    Preadditive.comp_sum]
  change Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (e * (n + 1) - 1) -
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (e * (n + 1 + 1) - 1) ≫
      X.asFunctor.map (homOfLE (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left e (Nat.le_succ (n + 1))) 1)).op = _
  let g (k : ℕ) : (∏ᶜ fun i : ℕ ↦ X.asFunctor.obj (op i)) ⟶
      X.asFunctor.obj (op (e * (n + 1) - 1)) :=
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (e * (n + 1) - 1 + k) ≫
      X.asFunctor.map (homOfLE (Nat.le_add_right (e * (n + 1) - 1) k)).op
  have heq : e * (n + 1 + 1) - 1 = e * (n + 1) - 1 + e := by
    have hp := Nat.mul_le_mul_left (n + 1) he
    simp only [Nat.mul_add, Nat.mul_one] at *
    omega
  have htel := Finset.sum_range_sub' g e
  have hlast : Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i))
      (e * (n + 1 + 1) - 1) ≫ X.asFunctor.map
        (homOfLE (Nat.sub_le_sub_right
          (Nat.mul_le_mul_left e (Nat.le_succ (n + 1))) 1)).op = g e := by
    dsimp only [g]
    have aux (m l : ℕ) (hm : e * (n + 1) - 1 ≤ m)
        (hl : e * (n + 1) - 1 ≤ l) (hml : m = l) :
        Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) m ≫
            X.asFunctor.map (homOfLE hm).op =
          Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) l ≫
            X.asFunctor.map (homOfLE hl).op := by
      subst l
      rfl
    exact aux _ _ _ _ heq
  rw [hlast]
  change _ = _ at htel
  convert htel.symm using 1
  · simp [g]
  · rw [Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [g]
    rw [← X.asFunctor.map_comp]
    congr 2

variable {B : Type v} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
private abbrev roosTowerMap (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (ComplexShape.up ℤ)
private noncomputable abbrev roosComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun n : ℕ ↦ X.asFunctor.obj (op n))
private theorem roosComparison_transition (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (strictRoosEndomorphism X) ≫
      roosComparison F X =
    roosComparison F X ≫ strictRoosEndomorphism ((roosTowerMap F).obj X) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  change G.map (towerTransitionEndomorphism _) ≫
    piComparison G (fun n : ℕ ↦ X.asFunctor.obj (op n)) =
    piComparison G (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
    towerTransitionEndomorphism (K := fun n : ℕ ↦ G.obj (X.asFunctor.obj (op n)))
      (fun n ↦ G.map (X.asFunctor.map (homOfLE
      (Nat.le_succ n)).op))
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Functor.map_id, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    piComparison_comp_π, Pi.lift_comp_π, Category.id_comp]
  rw [← G.map_comp, Pi.lift_comp_π]
  rw [← Category.assoc, piComparison_comp_π, ← G.map_comp]
private noncomputable def roosTheta (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [IsIso (roosComparison F X)] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (strictRoosComplex X) ≅
      strictRoosComplex ((roosTowerMap F).obj X) :=
  (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1)).app
    (CochainComplex.mappingCone (strictRoosEndomorphism X))) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso
      (homotopyCofiber.mapHomologicalComplexObjIso (strictRoosEndomorphism X) F ≪≫
        homotopyCofiber.mapArrowIso _ _
          (fun j : ℤ ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
          (Arrow.isoMk (asIso (roosComparison F X)) (asIso (roosComparison F X))
            (roosComparison_transition F X).symm))
omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem roos_XIsoOfEq (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ)
    {i j : ℤ} (h : i = j) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).XIsoOfEq h).hom =
      F.map (K.XIsoOfEq h).hom := by
  subst h
  change 𝟙 (F.obj (K.X i)) = F.map (𝟙 (K.X i))
  exact (F.map_id _).symm

set_option backward.isDefEq.respectTransparency false in
omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem roosConeFunctor_coordinates (F : A ⥤ B) [F.Additive]
    {P Q : CochainComplex A ℤ} (φ : P ⟶ Q) (p q : ℤ) (hpq : p + 1 = q) :
    (homotopyCofiber.mapHomologicalComplexObjXIso φ F p).hom ≫
        (homotopyCofiber.XIsoBiprod
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) p q hpq).hom =
      F.map (homotopyCofiber.XIsoBiprod φ p q hpq).hom ≫
        F.biprodComparison (P.X q) (Q.X p) := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' hpq
  simp [homotopyCofiber.mapHomologicalComplexObjXIso, Functor.biprodComparison]

set_option backward.isDefEq.respectTransparency false in
private theorem roosTheta_coordinates (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [IsIso (roosComparison F X)] (p : ℤ) :
    (roosTheta F X).hom.f (p + 1) ≫
      (strictRoosCoordinates ((roosTowerMap F).obj X) p).hom =
    F.map (strictRoosCoordinates X p).hom ≫
      F.biprodComparison ((strictRoosProduct X).X p) ((strictRoosProduct X).X (p + 1)) ≫
      biprod.map ((roosComparison F X).f p) ((roosComparison F X).f (p + 1)) := by
  dsimp only [roosTheta, Iso.trans_hom, Iso.app, Iso.symm_hom,
    Functor.mapIso_hom, HomologicalComplex.comp_f]
  simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f', HomologicalComplex.comp_f]
  dsimp only [strictRoosCoordinates, Iso.trans_hom]
  dsimp only [CochainComplex.shiftFunctorObjXIso]
  simp only [Category.assoc]
  rw [XIsoOfEq_hom_naturality_assoc]
  rw [XIsoOfEq_hom_naturality_assoc]
  simp only [roos_XIsoOfEq, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
    strictRoosComplex, CochainComplex.shiftFunctor_obj_X']
  simp only [Category.id_comp]
  apply (cancel_epi (F.map ((CochainComplex.mappingCone
    (strictRoosEndomorphism X)).XIsoOfEq
      (show p + 1 + -1 = p from by omega)).hom)).mpr
  simp only [homotopyCofiber.mapArrowIso_hom]
  rw [roosConeMap_coordinates]
  change (homotopyCofiber.mapHomologicalComplexObjXIso
      (strictRoosEndomorphism X) F p).hom ≫ _ = _
  rw [← Category.assoc, roosConeFunctor_coordinates]
  simp only [Category.assoc]
  congr 1
  apply biprod.hom_ext
  · simp only [Category.assoc]
    erw [biprod.map_fst, Functor.biprodComparison_fst_assoc]
    erw [biprod.braiding_hom, biprod.lift_fst_assoc,
      Functor.biprodComparison_snd_assoc, ← F.map_comp_assoc, biprod.lift_fst]
  · simp only [Category.assoc]
    erw [biprod.map_snd, Functor.biprodComparison_snd_assoc]
    erw [biprod.braiding_hom, biprod.lift_snd_assoc,
      Functor.biprodComparison_fst_assoc, ← F.map_comp_assoc, biprod.lift_snd]
set_option backward.isDefEq.respectTransparency false in
private theorem roosTheta_map (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    [IsIso (roosComparison F X)] [IsIso (roosComparison F Y)]
    (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (h : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b)
    (aB bB : strictRoosProduct ((roosTowerMap F).obj X) ⟶
      strictRoosProduct ((roosTowerMap F).obj Y))
    (hB : aB ≫ strictRoosEndomorphism ((roosTowerMap F).obj Y) =
      strictRoosEndomorphism ((roosTowerMap F).obj X) ≫ bB)
    (ha : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ roosComparison F Y =
      roosComparison F X ≫ aB)
    (hb : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map b ≫ roosComparison F Y =
      roosComparison F X ≫ bB) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (strictRoosMapOfSquare a b h) ≫
        (roosTheta F Y).hom =
      (roosTheta F X).hom ≫ strictRoosMapOfSquare aB bB hB := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (strictRoosCoordinates ((roosTowerMap F).obj Y) p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc, roosTheta_coordinates,
    strictRoosMapOfSquare_coordinates]
  change F.map ((strictRoosMapOfSquare a b h).f (p + 1)) ≫ _ = _
  rw [← Category.assoc, ← F.map_comp, strictRoosMapOfSquare_coordinates,
    F.map_comp, Category.assoc]
  rw [reassoc_of% roosTheta_coordinates F X p]
  congr 1
  have hbp := congrArg (fun f ↦ f.f p) hb
  have hap := congrArg (fun f ↦ f.f (p + 1)) ha
  apply biprod.hom_ext
  · simp only [Category.assoc]
    erw [biprod.map_fst, Functor.biprodComparison_fst_assoc,
      ← F.map_comp_assoc, biprod.map_fst]
    erw [biprod.map_fst, biprod.map_fst_assoc, Functor.biprodComparison_fst_assoc]
    rw [F.map_comp, Category.assoc]
    exact congrArg (fun f ↦ F.map biprod.fst ≫ f) hbp
  · simp only [Category.assoc]
    erw [biprod.map_snd, Functor.biprodComparison_snd_assoc,
      ← F.map_comp_assoc, biprod.map_snd]
    erw [biprod.map_snd, biprod.map_snd_assoc, Functor.biprodComparison_snd_assoc]
    rw [F.map_comp, Category.assoc]
    exact congrArg (fun f ↦ F.map biprod.snd ≫ f) hap

private theorem roosComparison_map (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (strictRoosProductMap f) ≫
        roosComparison F Y =
      roosComparison F X ≫ strictRoosProductMap ((roosTowerMap F).map f) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  change G.map (Limits.Pi.map (fun n : ℕ ↦
      (complexOfFunctorsToFunctorToComplex.map f).app (op n))) ≫
      piComparison G (fun n : ℕ ↦ (complexOfFunctorsToFunctorToComplex.obj Y).obj (op n)) =
    piComparison G (fun n : ℕ ↦ (complexOfFunctorsToFunctorToComplex.obj X).obj (op n)) ≫
      Limits.Pi.map (fun n : ℕ ↦
        G.map ((complexOfFunctorsToFunctorToComplex.map f).app (op n)))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc,
    piComparison_comp_π, Pi.map_π]
  rw [← G.map_comp, Pi.map_π]
  simp only [piComparison_comp_π_assoc, ← G.map_comp]

end CategoryTheory
