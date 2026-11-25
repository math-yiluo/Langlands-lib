/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison

/-! # Direct image and coefficient restrictions

## References

* Zheng Construction 4.1
* Stacks 03D2 and 03DA
* Stacks 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

variable (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
  (a : ∀ n, (I n).modules ⊣ V n)

private theorem normalized_right_restriction
    {A₁ A₂ B₁ B₂ S T : Type*}
    [Category A₁] [Category A₂] [Category B₁] [Category B₂] [Category S] [Category T]
    {L : S ⥤ T} {R : T ⥤ S} (adj : L ⊣ R)
    (U : A₁ ⥤ S) [U.Faithful] [U.ReflectsIsomorphisms] (W : B₁ ⥤ T)
    (X : A₂ ⥤ A₁) (Y : B₂ ⥤ B₁)
    {L₁ : A₁ ⥤ B₁} {L₂ : A₂ ⥤ B₂} {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ⋙ W ≅ U ⋙ L) (e₂ : L₂ ⋙ Y ⋙ W ≅ X ⋙ U ⋙ L)
    (d₁ : R₁ ⋙ U ≅ W ⋙ R) (d₂ : R₂ ⋙ X ⋙ U ≅ Y ⋙ W ⋙ R)
    (ρ : L₂ ⋙ Y ≅ X ⋙ L₁)
    (hρ : ∀ M, W.map (ρ.hom.app M) ≫ e₁.hom.app (X.obj M) = e₂.hom.app M)
    (ha₁ : ∀ M N (f : L₁.obj M ⟶ N),
      U.map (a₁.homEquiv M N f) ≫ d₁.hom.app N =
        adj.homEquiv _ _ (e₁.inv.app M ≫ W.map f))
    (ha₂ : ∀ M N (f : L₂.obj M ⟶ N),
      (X ⋙ U).map (a₂.homEquiv M N f) ≫ d₂.hom.app N =
        adj.homEquiv _ _ (e₂.inv.app M ≫ (Y ⋙ W).map f)) :
    ∃ δ : Y ⋙ R₁ ≅ R₂ ⋙ X,
      ∀ N, U.map (δ.hom.app N) ≫ d₂.hom.app N = d₁.hom.app (Y.obj N) := by
  have hρ' (M : A₂) : W.map (ρ.inv.app M) ≫ e₂.hom.app M =
      e₁.hom.app (X.obj M) := by
    have hh := congrArg (W.map (ρ.inv.app M) ≫ ·) (hρ M)
    simpa only [← Category.assoc, ← W.map_comp, Iso.inv_hom_id_app,
      W.map_id, Category.id_comp] using hh.symm
  let β (N : B₂) : X.obj (R₂.obj N) ⟶ R₁.obj (Y.obj N) :=
    a₁.homEquiv _ _ (ρ.inv.app (R₂.obj N) ≫ Y.map (a₂.counit.app N))
  have hb (N : B₂) : U.map (β N) ≫ d₁.hom.app (Y.obj N) = d₂.hom.app N := by
    rw [ha₁]
    have hi : e₁.inv.app (X.obj (R₂.obj N)) ≫ W.map (ρ.inv.app (R₂.obj N)) =
        e₂.inv.app (R₂.obj N) := by
      apply (cancel_mono (e₂.hom.app (R₂.obj N))).1
      simp only [Category.assoc, hρ', Iso.inv_hom_id_app]
      rfl
    rw [W.map_comp, ← Category.assoc, hi]
    have hn := ha₂ (R₂.obj N) N (a₂.counit.app N)
    have hc : a₂.homEquiv _ N (a₂.counit.app N) = 𝟙 _ := by
      apply (a₂.homEquiv _ N).symm.injective
      rw [Equiv.symm_apply_apply, a₂.homEquiv_symm_id]
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn ⊢
    simpa only [hc, CategoryTheory.Functor.map_id, Category.id_comp] using hn.symm
  have hi (N : B₂) : IsIso (β N) := by
    have hmap : U.map (β N) = d₂.hom.app N ≫ d₁.inv.app (Y.obj N) := by
      apply (cancel_mono (d₁.hom.app (Y.obj N))).1
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact (hb N).trans (Category.comp_id _).symm
    have : IsIso (U.map (β N)) := by rw [hmap]; infer_instance
    exact isIso_of_reflects_iso _ U
  have hinv (N : B₂) : U.map (inv (β N)) =
      d₁.hom.app (Y.obj N) ≫ d₂.inv.app N := by
    apply (cancel_epi (U.map (β N))).1
    rw [← U.map_comp, IsIso.hom_inv_id, U.map_id]
    rw [← Category.assoc, hb, Iso.hom_inv_id_app]
    rfl
  let δ : Y ⋙ R₁ ≅ R₂ ⋙ X :=
    NatIso.ofComponents (fun N ↦ (asIso (β N)).symm) (by
      intro M N f
      apply U.map_injective
      simp only [Functor.map_comp, Iso.symm_hom, asIso_inv, hinv, Category.assoc]
      have h₁ := d₁.hom.naturality (Y.map f)
      have h₂ := d₂.inv.naturality f
      dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ ⊢
      rw [← Category.assoc, h₁, Category.assoc, h₂])
  refine ⟨δ, ?_⟩
  intro N
  change U.map (inv (β N)) ≫ _ = _
  rw [hinv, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem directRestrictionComparison
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f))
    {m n : ℕ} (h : n ≤ m)
    (ρ : (I n).modules ⋙ res (coefficientMap J' F σ h) ≅
      res (coefficientMap J B τ h) ⋙ (I m).modules)
    (hρ : ∀ M : Mod.{c, v, max c v r} J (B n),
      (underlying.{c, v, r} J' (F m)).map (ρ.hom.app M) ≫
          (I m).moduleUnderlying.hom.app ((res (coefficientMap J B τ h)).obj M) =
        (I n).moduleUnderlying.hom.app M) :
    ∃ δ : res (coefficientMap J' F σ h) ⋙ V m ≅
        V n ⋙ res (coefficientMap J B τ h),
      ∀ N : Mod.{c, v, max c v r} J' (F n),
        (underlying.{c, v, r} J (B m)).map (δ.hom.app N) ≫ (eV n).hom.app N =
          (eV m).hom.app ((res (coefficientMap J' F σ h)).obj N) := by
  exact normalized_right_restriction adjSet
    (underlying.{c, v, r} J (B m)) (underlying.{c, v, r} J' (F m))
    (res (coefficientMap J B τ h)) (res (coefficientMap J' F σ h))
    (a m) (a n) (I m).moduleUnderlying (I n).moduleUnderlying (eV m) (eV n)
    ρ hρ (ha m) (ha n)

/-- Normalized direct-image comparisons for every coefficient restriction. -/
structure DirectRestrictions
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush) where
  iso : ∀ {m n : ℕ} (h : n ≤ m),
    res (coefficientMap J' F σ h) ⋙ V m ≅ V n ⋙ res (coefficientMap J B τ h)
  normalized : ∀ {m n : ℕ} (h : n ≤ m) (N : Mod.{c, v, max c v r} J' (F n)),
    (underlying.{c, v, r} J (B m)).map ((iso h).hom.app N) ≫ (eV n).hom.app N =
      (eV m).hom.app ((res (coefficientMap J' F σ h)).obj N)

section DirectRestrictionConstruction

/-- The level right adjoints commute with compatible coefficient restrictions. -/
theorem directRestrictions_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    Nonempty (DirectRestrictions.{c, v, r} J B τ J' F σ V uPush eV) := by
  classical
  let α : rings J B τ ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r}) ⋙
      uInv ⟶ rings J' F σ ⋙
        sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r}) :=
    NatTrans.ofOpSequence (fun n ↦ (I n).ringUnderlying.hom) (by
      intro n
      simpa only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ]
        using hI n)
  have hc {m n : ℕ} (h : n ≤ m) :
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map
          (coefficientMap J B τ h)) ≫ (I n).ringUnderlying.hom =
        (I m).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map
            (coefficientMap J' F σ h) := α.naturality (homOfLE h).op
  have hδ {m n : ℕ} (h : n ≤ m) :
      ∃ δ : res (coefficientMap J' F σ h) ⋙ V m ≅
          V n ⋙ res (coefficientMap J B τ h),
        ∀ N : Mod.{c, v, max c v r} J' (F n),
          (underlying.{c, v, r} J (B m)).map (δ.hom.app N) ≫ (eV n).hom.app N =
            (eV m).hom.app ((res (coefficientMap J' F σ h)).obj N) := by
    obtain ⟨ρ, hρ⟩ := SheafOfModules.InverseImageScalarRestriction.exists_comparison
      (I m) (I n) (coefficientMap J B τ h) (coefficientMap J' F σ h) (hc h)
    exact directRestrictionComparison.{c, v, r} J B τ J' uInv F σ I V a
      uPush adjSet eV ha h ρ hρ
  exact ⟨{ iso := fun h ↦ (hδ h).choose, normalized := fun h ↦ (hδ h).choose_spec }⟩

end DirectRestrictionConstruction

end WeilConjectures.SemilinearSections
end
