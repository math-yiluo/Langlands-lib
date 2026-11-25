/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-! The explicit strict Roos cone and its ordinary-limit inclusion.
Source: Stacks Project, Cohomology on Sites, Tag 0941, proof of
lemma-derived-limit-is-ok (auxiliary; not a blueprint node). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

section Construction

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

noncomputable abbrev roosP (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex A ℤ := ∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))

noncomputable abbrev roosU (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosP X ⟶ roosP X :=
  towerTransitionEndomorphism
    (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)

noncomputable abbrev roosPmap {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    roosP X ⟶ roosP Y :=
  Limits.Pi.map (fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))

lemma roosPmap_id (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosPmap (𝟙 X) = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  simp only [roosPmap, Pi.map_π, Functor.map_id, NatTrans.id_app]
  change _ ≫ 𝟙 _ = _
  simp

lemma roosPmap_comp {X Y Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) : roosPmap (f ≫ g) = roosPmap f ≫ roosPmap g := by
  apply Pi.hom_ext
  intro n
  simp [roosPmap, Category.assoc]

lemma roosU_natural {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    roosU X ≫ roosPmap f = roosPmap f ≫ roosU Y := by
  symm
  apply towerTransitionEndomorphism_natural_backward
  intro n
  exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality
    (homOfLE (Nat.le_succ n)).op).symm

noncomputable def roosConeFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj X := CochainComplex.mappingCone (roosU X)
  map f := CochainComplex.mappingCone.map _ _ (roosPmap f) (roosPmap f) (roosU_natural f)
  map_id X := by
    simpa only [roosPmap_id] using CochainComplex.mappingCone.map_id (roosU X)
  map_comp f g := by
    simpa only [roosPmap_comp] using
      CochainComplex.mappingCone.map_comp _ _ _ (roosPmap f) (roosPmap f)
        (roosU_natural f) (roosPmap g) (roosPmap g) (roosU_natural g)

/-- The strict Roos functor: the shifted mapping cone of one minus transition shift on
termwise products of a tower complex. Its maps are the shifted cone maps induced by
products of strict tower morphisms.
Source: Stacks Project, Cohomology on Sites, Tag 0941, proof of
lemma-derived-limit-is-ok (auxiliary; not a blueprint node). -/
noncomputable def roosF :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  roosConeFunctor ⋙ shiftFunctor _ (-1 : ℤ)

noncomputable def roosχ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ≅ (roosP X).X p ⊞ (roosP X).X (p + 1) :=
  (CochainComplex.mappingCone (roosU X)).shiftFunctorObjXIso
      (-1) (p + 1) p (add_neg_cancel_right p 1).symm ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) p (p + 1) rfl ≪≫
      biprod.braiding _ _

noncomputable def roosProj (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosF.obj X ⟶ roosP X :=
  -((CochainComplex.mappingCone.fst (roosU X)).leftShift (-1) 0 (by omega)).homOf

lemma roosProj_f (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosProj X).f (p + 1) = (roosχ X p).hom ≫ biprod.snd := by
  simp [roosProj, roosχ, CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX]

lemma roosF_map_χ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ) :
    (roosF.map f).f (p + 1) ≫ (roosχ Y p).hom =
      (roosχ X p).hom ≫ biprod.map ((roosPmap f).f p) ((roosPmap f).f (p + 1)) := by
  dsimp only [roosF, Functor.comp_map, roosConeFunctor, roosχ, Iso.trans_hom]
  rw [CochainComplex.shiftFunctor_map_f']
  simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
  simp only [Category.assoc]
  congr 1
  apply CochainComplex.mappingCone.ext_from (roosU X) (p + 1) p rfl
  · change (CochainComplex.mappingCone.inl (roosU X)).v (p + 1) p (by omega) ≫
        (CochainComplex.mappingCone.map _ _ (roosPmap f) (roosPmap f)
          (roosU_natural f)).f p ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
    simp only [CochainComplex.mappingCone.inl,
      CochainComplex.HomComplex.Cochain.mk_v, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply biprod.hom_ext <;> simp
  · rw [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc]
    simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
    apply biprod.hom_ext <;> simp

noncomputable def roosLift {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (α : P ⟶ roosP X) (hα : α ≫ roosU X = 0) :
    P ⟶ roosF.obj X :=
  CochainComplex.mappingCocone.lift (roosU X) α 0 (by simp [hα])

lemma roosLift_χ {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (α : P ⟶ roosP X) (hα : α ≫ roosU X = 0) (p : ℤ) :
    (roosLift α hα).f (p + 1) ≫ (roosχ X p).hom = biprod.lift 0 (α.f (p + 1)) := by
  apply biprod.hom_ext
  · have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' hq
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dite_eq_left hq]
    have h := CochainComplex.mappingCocone.lift_f_snd_v (roosU X) α 0
        (by simp [hα]) (p + 1) p (by omega)
    simpa [roosLift, roosχ, CochainComplex.mappingCocone.snd,
      CochainComplex.HomComplex.Cochain.leftShift_v, Category.assoc,
      show Int.negOnePow 2 = 1 by rfl, CochainComplex.mappingCone.snd,
      hs p (p + 1) rfl] using h
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← roosProj_f]
    exact CochainComplex.mappingCocone.lift_f_fst_f _ _ _ _ _

noncomputable def roosEval (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    roosF.obj X ⟶ X.asFunctor.obj (op n) := roosProj X ≫ Pi.π _ n

lemma roosEval_f (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (p : ℤ) :
    (roosEval X n).f (p + 1) =
      (roosχ X p).hom ≫ biprod.snd ≫
        (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (p + 1) := by
  simp only [roosEval, HomologicalComplex.comp_f, roosProj_f, Category.assoc]

lemma roosEval_natural {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (n : ℕ) :
    roosF.map f ≫ roosEval Y n = roosEval X n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (roosF.map f ≫ roosEval Y n).f (p + 1) =
    (roosEval X n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)).f (p + 1)
  simp only [HomologicalComplex.comp_f, roosEval_f, reassoc_of% roosF_map_χ,
    biprod.map_snd_assoc]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Pi.map_π]
  simp [HomologicalComplex.comp_f, Category.assoc]

lemma roos_compatible {B : Type*} [Category* B] (X : ℕᵒᵖ ⥤ B) {P : B}
    (γ : ∀ n : ℕ, P ⟶ X.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.map (homOfLE (Nat.le_succ n)).op = γ n)
    {n m : ℕ} (h : n ≤ m) : γ m ≫ X.map (homOfLE h).op = γ n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, X.map_comp, ← Category.assoc, hγ, ih]

noncomputable def roosAugment {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    P ⟶ roosF.obj X :=
  roosLift (Pi.lift γ) (by
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hγ]
)

lemma roosAugment_χ {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (p : ℤ) : (roosAugment γ hγ).f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 ((Pi.lift γ).f (p + 1)) := roosLift_χ _ _ _

variable [HasLimitsOfShape ℕᵒᵖ A]

noncomputable def roosι (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limit X.asFunctor ⟶ roosF.obj X :=
  roosLift (Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))) (by
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, limit.w]
)

lemma roosι_χ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosι X).f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) :=
  roosLift_χ _ _ _

lemma roosι_natural {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) :
    lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫ roosι Y =
      roosι X ≫ roosF.map f := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫
    roosι Y).f (p + 1) = (roosι X ≫ roosF.map f).f (p + 1)
  apply (cancel_mono (roosχ Y p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc, roosι_χ, roosF_map_χ]
  rw [← Category.assoc, roosι_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp [roosPmap]

lemma roosι_eval (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    roosι X ≫ roosEval X n = limit.π X.asFunctor (op n) := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (roosι X ≫ roosEval X n).f (p + 1) = _
  simp only [HomologicalComplex.comp_f, roosEval_f, reassoc_of% roosι_χ,
    biprod.lift_snd_assoc]
  simp [← HomologicalComplex.comp_f]

noncomputable def roosAugmentLimit {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    P ⟶ limit X.asFunctor :=
  limit.lift X.asFunctor
    { pt := P
      π :=
        { app := fun n ↦ γ n.unop
          naturality := by
            intro n m f
            change 𝟙 P ≫ γ m.unop = γ n.unop ≫ X.asFunctor.map f
            rw [Category.id_comp]
            have he : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
            simpa only [he] using (roos_compatible X.asFunctor γ hγ
              (leOfHom f.unop)).symm } }

omit [HasCountableProducts A] in
lemma roosAugmentLimit_π {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (n : ℕ) : roosAugmentLimit γ hγ ≫ limit.π X.asFunctor (op n) = γ n :=
  limit.lift_π _ _

lemma roosAugment_eq {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    roosAugment γ hγ = roosAugmentLimit γ hγ ≫ roosι X := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (roosAugment γ hγ).f (p + 1) =
    (roosAugmentLimit γ hγ ≫ roosι X).f (p + 1)
  apply (cancel_mono (roosχ X p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc, roosAugment_χ, roosι_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp [roosAugmentLimit_π]

noncomputable def roosLimitFunctor : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim

noncomputable def roosInclusion : roosLimitFunctor ⟶ roosF (A := A) where
  app := roosι
  naturality := fun _ _ f ↦ roosι_natural f

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

noncomputable def roosDerivedUnit
    {CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
    (κ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF) :
    roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ CF :=
  Functor.whiskerRight roosInclusion DerivedCategory.Q ≫ κ.hom

end Construction

end CategoryTheory
