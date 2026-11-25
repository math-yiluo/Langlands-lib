/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions

/-! The scalar mate identity for the normalized finite-free beta.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint

private theorem conjugate_pushHom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : F₁ ⊣ U₁) (b₂ : F₂ ⊣ U₂)
    (e : F₂ ⋙ R₂ ≅ R₁ ⋙ F₁) (θ : F₁ ⋙ L₂ ≅ L₁ ⋙ F₂)
    (hθ : θ.hom = Adjunction.pushHomOfComapIso a₁ a₂ e) :
    conjugateEquiv (a₁.comp b₂) (b₁.comp a₂) θ.hom =
      (mateEquiv b₂ b₁ (TwoSquare.mk _ _ _ _ e.inv)) := by
  have hm : mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ θ.hom) =
      TwoSquare.mk _ _ _ _ e.inv := by
    rw [hθ]
    exact (mateEquiv a₁ a₂).apply_symm_apply (TwoSquare.mk _ _ _ _ e.inv)
  have h := iterated_mateEquiv_conjugateEquiv a₁ a₂ b₁ b₂
    (TwoSquare.mk _ _ _ _ θ.hom)
  rw [hm] at h
  exact h.symm

private theorem mate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A) (N : B) (v : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map v) =
      G.map (adj.homEquiv M N v) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).naturality v
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

private theorem scalar_projection
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [MonoidalCategory A] [MonoidalCategory C]
    {L : A ⥤ C} {R : C ⥤ A} {L' : B ⥤ D} {R' : D ⥤ B}
    {E : A ⥤ B} {V : B ⥤ A} {E' : C ⥤ D} {V' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (s : L' ⋙ V' ≅ V ⋙ L) (θ : L ⋙ E' ≅ E ⋙ L')
    (d : R' ⋙ V ≅ V' ⋙ R)
    (hd : d.hom = (mateEquiv adj' adj (TwoSquare.mk _ _ _ _ s.inv)))
    {BY : A} {BX : C} (βY : tensorLeft BY ≅ E ⋙ V) (βX : tensorLeft BX ≅ E' ⋙ V')
    (μ : ∀ M N : A, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N) (e : L.obj BY ≅ BX)
    (hpull : ∀ M : A,
      L.map (βY.hom.app M) ≫ s.inv.app (E.obj M) ≫ V'.map (θ.inv.app M) =
        μ BY M ≫ (e.hom ⊗ₘ 𝟙 (L.obj M)) ≫ βX.hom.app (L.obj M)) (K : C) :
    βY.hom.app (R.obj K) ≫
        V.map (adj'.homEquiv _ _ (θ.inv.app (R.obj K) ≫ E'.map (adj.counit.app K))) ≫
        d.hom.app (E'.obj K) ≫ R.map (βX.inv.app K) =
      adj.homEquiv _ _ (μ BY (R.obj K) ≫ (e.hom ⊗ₘ adj.counit.app K)) := by
  have ht := mate_adjunct adj' adj (TwoSquare.mk _ _ _ _ s.inv) _ _
    (θ.inv.app (R.obj K) ≫ E'.map (adj.counit.app K))
  change adj.homEquiv _ _
      (s.inv.app (E.obj (R.obj K)) ≫ V'.map _) =
    V.map _ ≫ (mateEquiv adj' adj (TwoSquare.mk _ _ _ _ s.inv)).app
      (E'.obj K) at ht
  rw [hd]
  slice_lhs 2 3 => rw [← ht]
  erw [← adj.homEquiv_naturality_right
    (s.inv.app (E.obj (R.obj K)) ≫
      V'.map (θ.inv.app (R.obj K) ≫ E'.map (adj.counit.app K))) (βX.inv.app K)]
  erw [← adj.homEquiv_naturality_left (βY.hom.app (R.obj K))]
  apply adj.homEquiv _ _ |>.congr_arg
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 1 3 => rw [hpull]
  have hn := βX.hom.naturality (adj.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Category.assoc]
  erw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  congr 1
  exact (tensorHom_comp_whiskerLeft e.hom (𝟙 _) (adj.counit.app K)).trans
    (by rw [Category.id_comp])

-- Instantiating the generic mate calculation compares large derived-functor interfaces.
/--
This is the mate step after the normalized construction and its
pullback square have been supplied.
-/
theorem finiteFreeScalarDerivedComparison_beta_mate
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z))
    (hpull : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
        (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj K) ≫
        (restriction a X).map ((D.theta a f).inv.app K) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj K)) :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
      (β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
        (restriction a Y).map (gamma D a f K) ≫
        (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
        (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K) =
      projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
        (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K := by
  have _ := hβ
  intro X Y f K
  let d := derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
  have hd : (restrictionPush D a f).hom =
      (mateEquiv (geometricAdjunction Λ' f) (geometricAdjunction Λ f)
        (TwoSquare.mk _ _ _ _ d.inv)) :=
    conjugate_pushHom (scalarAdjunction a Y) (scalarAdjunction a X)
      (geometricAdjunction Λ f) (geometricAdjunction Λ' f) d (D.theta a f)
      (D.thetaNormalization a f)
  exact scalar_projection (geometricAdjunction Λ f) (geometricAdjunction Λ' f)
    d (D.theta a f) (restrictionPush D a f) hd (β Y) (β X)
    (tensorPull Λ f) (modelPull Λ S f) (hpull X Y f) K

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
