/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Higher direct images to the spectrum of a field

Let `f : X ⟶ Spec K` be a morphism to the spectrum of a field. The global sections of the higher
direct image `R^q f_* ℱ` are the sheaf cohomology `H^q(X, ℱ)`, naturally in the `𝒪_X`-module
`ℱ` (`AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H_of_field`).

Since `Spec K` has a single point, taking global sections of sheaves on it is exact. Hence
`ℱ ↦ Γ(Spec K, R^q f_* ℱ)` is, like `ℱ ↦ H^q(X, ℱ)`, a cohomological δ-functor on `X.Modules`,
effaceable since injective `𝒪_X`-modules are acyclic for both; the two agree in degree `0`, so
they agree in all degrees (`CategoryTheory.ObjectProperty.nonempty_iso_of_connecting`).

This is the case `T = Spec K` of
`AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`, without its
hypotheses on `f` and `ℱ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section OnePoint

variable (T : Scheme.{u})

/-- The global sections of a sheaf of modules on `T`, as an abelian group. -/
noncomputable abbrev Γab : T.Modules ⥤ AddCommGrpCat.{u} :=
  toAb T ⋙ sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance : (Γab T).Additive where
  map_add := rfl

variable {T} [Subsingleton T] [Nonempty T]

/-- On a scheme with a single point, an epimorphism of abelian sheaves is surjective on global
sections. -/
lemma surjective_app_top_of_epi {A B : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    (g : A ⟶ B) [Epi g] : Function.Surjective (g.hom.app (op ⊤)) := by
  intro s
  obtain ⟨x⟩ := ‹Nonempty T›
  have := (TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance
  obtain ⟨W, hW, ⟨t, ht⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp this ⊤ s x trivial
  obtain rfl : W = ⊤ := eq_top_iff.2 fun y _ ↦ Subsingleton.elim x y ▸ hxW
  refine ⟨t, ht.trans ?_⟩
  exact congrArg (fun φ ↦ B.obj.map φ s) (Subsingleton.elim _ (𝟙 _)) |>.trans
    (by rw [B.obj.map_id]; rfl)

instance : (Γab T).PreservesEpimorphisms where
  preserves g _ := (AddCommGrpCat.epi_iff_surjective _).2
    (surjective_app_top_of_epi ((toAb T).map g))

instance : (Γab T).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end OnePoint

variable {X : Scheme.{u}} {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
  [HasInjectiveResolutions X.Modules]

instance : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))

instance : Nonempty (Spec (.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))

/-- The global sections of the pushforward along `f : X ⟶ Spec K` are the global sections. -/
noncomputable def pushforwardCompΓabIso :
    pushforward f ⋙ Γab (Spec (.of K)) ≅ toAb X ⋙ sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op ⊤) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- **Higher direct images to a point compute cohomology.** For `f : X ⟶ Spec K`, the functors
`ℱ ↦ Γ(Spec K, R^q f_* ℱ)` and `ℱ ↦ H^q(X, ℱ)` on `X.Modules` are isomorphic. -/
theorem nonempty_higherDirectImage_comp_Γab_iso_functorH (q : ℕ) :
    Nonempty ((⊤ : ObjectProperty X.Modules).ι ⋙ higherDirectImage f q ⋙
        Γab (Spec (.of K)) ≅
      (⊤ : ObjectProperty X.Modules).ι ⋙ toAb X ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q) := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := X.Modules)
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (Spec (.of K)).Modules
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  refine (⊤ : ObjectProperty X.Modules).nonempty_iso_of_connecting (fun _ _ ↦ ⟨trivial, trivial⟩)
    (fun q ↦ higherDirectImage f q ⋙ Γab (Spec (.of K)))
    (fun q ↦ toAb X ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q)
    (fun S hS _ q ↦ (Γab (Spec (.of K))).map (hS.rightDerivedδ (pushforward f) q))
    (fun S hS _ q ↦ CategoryTheory.Sheaf.functorHδ (shortExact_map_toSheaf hS) q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    change (Γab _).map _ ≫ (Γab _).map ((higherDirectImage f (q + 1)).map φ.τ₁) =
      (Γab _).map ((higherDirectImage f q).map φ.τ₃) ≫ (Γab _).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (ShortComplex.ShortExact.rightDerivedδ_naturality (pushforward f) h₁ h₂ φ q)
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (shortExact_map_toSheaf h₁) q
      (shortExact_map_toSheaf h₂) ((toAb X).mapShortComplex.map φ)
  · intro S hS _ q x
    have h := (ShortComplex.ab_exact_iff _).1
      ((hS.rightDerivedδ_exact₂ (pushforward f) q).map (Γab (Spec (.of K))))
    refine ⟨fun hx ↦ h x hx, ?_⟩
    rintro ⟨y, rfl⟩
    change ((Γab _).map ((higherDirectImage f q).map S.g) ≫
      (Γab _).map (hS.rightDerivedδ (pushforward f) q)) y = 0
    rw [← Functor.map_comp]
    erw [hS.comp_rightDerivedδ (pushforward f) q, Functor.map_zero]
    rfl
  · intro S hS _ q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (shortExact_map_toSheaf hS) q x
  · intro S hS _ q hinj y
    have h := (ShortComplex.ab_exact_iff _).1
      ((hS.rightDerivedδ_exact₃ (pushforward f) q).map (Γab (Spec (.of K))))
    have hz : IsZero ((Γab (Spec (.of K))).obj ((higherDirectImage f (q + 1)).obj S.X₂)) :=
      (Γab (Spec (.of K))).map_isZero
        ((pushforward f).isZero_rightDerived_obj_injective_succ q S.X₂)
    exact h y ((AddCommGrpCat.isZero_iff_subsingleton.1 hz).elim _ _)
  · intro S hS _ q hinj
    have : Subsingleton (CategoryTheory.Sheaf.H (S.map (toAb X)).X₂ (q + 1)) :=
      subsingleton_H_of_injective S.X₂ q
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (shortExact_map_toSheaf hS) q
  · exact Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight ((pushforward f).rightDerivedZeroIsoSelf) _ ≪≫
        pushforwardCompΓabIso f ≪≫ Functor.isoWhiskerLeft (toAb X)
          (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop).symm)

/-- **The sections of the higher direct images to the spectrum of a field.** For
`f : X ⟶ Spec K`, the global sections of `R^q f_* ℱ` are the sheaf cohomology `H^q(X, ℱ)`, by
additive isomorphisms natural in the `𝒪_X`-module `ℱ`.

This is the case `T = Spec K` of
`AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`, which holds
here for every `f` and `ℱ`. -/
theorem exists_addEquiv_sections_higherDirectImage_H_of_field (q : ℕ) :
    ∃ e : ∀ ℱ : X.Modules, Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q,
      ∀ (ℱ 𝒢 : X.Modules) (φ : ℱ ⟶ 𝒢) (x : Γ((higherDirectImage f q).obj ℱ, ⊤)),
        e 𝒢 (((higherDirectImage f q).map φ).app ⊤ x) = H.map φ q (e ℱ x) := by
  obtain ⟨i⟩ := nonempty_higherDirectImage_comp_Γab_iso_functorH f q
  refine ⟨fun ℱ ↦ (i.app ⟨ℱ, trivial⟩).addCommGroupIsoToAddEquiv, fun ℱ 𝒢 φ x ↦ ?_⟩
  exact ConcreteCategory.congr_hom (i.hom.naturality
    (ObjectProperty.homMk φ : (⟨ℱ, trivial⟩ : (⊤ : ObjectProperty X.Modules).FullSubcategory) ⟶
      ⟨𝒢, trivial⟩)) x

/-- **The sections of the higher direct images to the spectrum of a field, linearly.** For
`f : X ⟶ Spec K`, `Γ(Spec K, R^q f_* ℱ) ≅ H^q(X, ℱ)` by an isomorphism which is linear along
`f^♯ : Γ(Spec K, ⊤) → Γ(X, ⊤)`. -/
theorem exists_bijective_semilinearMap_sections_higherDirectImage_H_of_field (ℱ : X.Modules)
    (q : ℕ) :
    ∃ e : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₛₗ[f.appTop.hom] ℱ.H q, Function.Bijective e := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_higherDirectImage_H_of_field f q
  refine ⟨{ toFun := e ℱ, map_add' := map_add _, map_smul' := fun a x ↦ ?_ }, (e ℱ).bijective⟩
  have h : a • x = ((higherDirectImage f q).map (ℱ.smulHom (f.appTop a))).app ⊤ x := by
    rw [higherDirectImage_map_smulHom, smulHom_app_apply]
    congr 1
  rw [h, he]
  rfl

end AlgebraicGeometry.Scheme.Modules
