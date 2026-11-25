/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering

/-! # Full faithfulness of restriction to resolving representatives -/

-- After dropping the copy of upstream's declaration, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory

-- Resolve the new vertices in Ore squares, roofs, and common refinements.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem restriction_localization
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  have : V.HasRightCalculusOfFractions :=
    { exists_rightFraction := by
        intro X Y φ
        obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk φ.f.hom φ.s.hom φ.hs
          : W.LeftFraction X.obj Y.obj).exists_rightFraction
        obtain ⟨Z, r, hr⟩ := res ψ.X'
        refine ⟨MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (r ≫ ψ.s)) (W.comp_mem _ _ hr ψ.hs)
          (ObjectProperty.homMk (r ≫ ψ.f)), ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hψ).trans
          (Category.assoc _ _ _).symm)
      ext := by
        intro X Y Y' f g s hs h
        obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
          f.hom g.hom s.hom hs (congrArg (fun k ↦ k.hom) h)
        obtain ⟨T, r, hr⟩ := res Z
        refine ⟨T, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) heq).trans
          (Category.assoc _ _ _).symm) }
  let h : V.IsInvertedBy (P.ι ⋙ L) := fun _ _ s hs ↦ Localization.inverts L W s.hom hs
  let F := Localization.Construction.lift (P.ι ⋙ L) h
  have fac : V.Q ⋙ F = P.ι ⋙ L := Localization.Construction.fac _ _
  have fmap {X Y : P.FullSubcategory} (f : X ⟶ Y) :
      F.map (V.Q.map f) = L.map f.hom := by
    simpa using (eqToIso fac).hom.naturality f
  have hf : F.Full := by
    refine ⟨?_⟩
    intro X Y f
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W
      (show L.obj X₀.obj ⟶ L.obj Y₀.obj from f)
    obtain ⟨Z, r, hr⟩ := res φ.X'
    let ψ : V.RightFraction X₀ Y₀ := MorphismProperty.RightFraction.mk
      (ObjectProperty.homMk (r ≫ φ.s)) (W.comp_mem _ _ hr φ.hs)
      (ObjectProperty.homMk (r ≫ φ.f))
    refine ⟨ψ.map V.Q (Localization.inverts _ _), ?_⟩
    have : IsIso (L.map r) := Localization.inverts L W r hr
    have : IsIso (L.map φ.s) := Localization.inverts L W φ.s φ.hs
    have : IsIso (L.map (r ≫ φ.s)) :=
      Localization.inverts L W _ (W.comp_mem _ _ hr φ.hs)
    simp only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv, fmap]
    change inv (L.map (r ≫ φ.s)) ≫ L.map (r ≫ φ.f) = f
    rw [hφ]
    simp [MorphismProperty.RightFraction.map]
  have hfaith : F.Faithful := by
    refine ⟨?_⟩
    intro X Y f g heq
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from f)
    obtain ⟨ψ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from g)
    let φ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk φ.s.hom φ.hs φ.f.hom
    let ψ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk ψ.s.hom ψ.hs ψ.f.hom
    have heq' : φ'.map L (Localization.inverts _ _) =
        ψ'.map L (Localization.inverts _ _) := by
      simpa only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv,
        fmap] using heq
    obtain ⟨Z, a, b, hs, hf, hw⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff L W φ' ψ').1 heq'
    obtain ⟨T, r, hr⟩ := res Z
    apply (MorphismProperty.RightFraction.map_eq_iff V.Q V φ ψ).2
    refine ⟨T, ObjectProperty.homMk (r ≫ a), ObjectProperty.homMk (r ≫ b), ?_, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans
        (Category.assoc _ _ _).symm)
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hf).trans
        (Category.assoc _ _ _).symm)
    · change W ((r ≫ a) ≫ φ.s.hom)
      rw [Category.assoc]
      exact W.comp_mem _ _ hr hw
  have hess : F.EssSurj := by
    refine ⟨?_⟩
    intro X
    have := Localization.essSurj L W
    let Y := L.objPreimage X
    let e := L.objObjPreimageIso X
    obtain ⟨Z, r, hr⟩ := res Y
    exact ⟨V.Q.obj Z, ⟨Localization.isoOfHom L W r hr ≪≫ e⟩⟩
  have : F.IsEquivalence := { }
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V (eqToIso fac)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fullyFaithfulWhiskeringOfFullEssSurj
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (p : C ⥤ D) [p.Full] [p.EssSurj]
    (E : Type u₃) [Category.{v₃} E] :
    ((whiskeringLeft C D E).obj p).FullyFaithful := by
  classical
  let L := (whiskeringLeft C D E).obj p
  have hfaith : L.Faithful := ⟨by
    intro A B a b h
    ext X
    apply (cancel_epi (A.map (p.objObjPreimageIso X).hom)).1
    rw [a.naturality, b.naturality]
    exact congrArg (fun z ↦ z ≫ B.map (p.objObjPreimageIso X).hom)
      (congrArg (fun z ↦ z.app (p.objPreimage X)) h)⟩
  have hfull : L.Full := ⟨by
    intro A B a
    let b : A ⟶ B :=
      { app X := A.map (p.objObjPreimageIso X).inv ≫
          a.app (p.objPreimage X) ≫ B.map (p.objObjPreimageIso X).hom
        naturality := by
          intro X Y g
          have ha := a.naturality (p.preimage
            ((p.objObjPreimageIso X).hom ≫ g ≫ (p.objObjPreimageIso Y).inv))
          change A.map (p.map _) ≫ _ = _ ≫ B.map (p.map _) at ha
          rw [p.map_preimage] at ha
          simp only [Functor.map_comp] at ha
          apply (cancel_epi (A.map (p.objObjPreimageIso X).hom)).1
          simp only [Category.assoc, ← A.map_comp_assoc, Iso.hom_inv_id, A.map_id,
            Category.id_comp]
          simp only [Functor.map_comp] at *
          rw [← Category.assoc, ha]
          simp only [Category.assoc, ← B.map_comp, Iso.inv_hom_id,
            Category.comp_id] }
    refine ⟨b, ?_⟩
    ext X
    have ha := a.naturality (p.preimage (p.objObjPreimageIso (p.obj X)).hom)
    change A.map (p.map _) ≫ _ = _ ≫ B.map (p.map _) at ha
    rw [p.map_preimage] at ha
    change A.map (p.objObjPreimageIso (p.obj X)).inv ≫
      a.app (p.objPreimage (p.obj X)) ≫ B.map (p.objObjPreimageIso (p.obj X)).hom = a.app X
    rw [← ha, ← A.map_comp_assoc, Iso.inv_hom_id, A.map_id, Category.id_comp]⟩
  exact Functor.FullyFaithful.ofFullyFaithful L

end CategoryTheory
