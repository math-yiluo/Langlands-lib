/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-! # Descent of bifunctor isomorphisms from K-flat models

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-kflat-bifunctor-iso-descent).
-/

@[expose] public section

universe uModel wModel uE vE

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance kFlatBifunctorDescentModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

noncomputable local instance kFlatBifunctorDescentModuleSymmetric (S : Scheme.{uModel}) :
    SymmetricCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.symmetricCategory S.sheaf

noncomputable local instance kFlatBifunctorDescentModulePreadditive (S : Scheme.{uModel}) :
    MonoidalPreadditive (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).1

noncomputable local instance kFlatBifunctorDescentModuleClosed (S : Scheme.{uModel}) :
    MonoidalClosed (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1

local instance kFlatBifunctorDescentModuleGrothendieck (S : Scheme.{uModel}) :
    IsGrothendieckAbelian.{uModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings S.toRingedSpace)

local instance kFlatBifunctorDescentModuleResolutions (S : Scheme.{uModel}) :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution S

/-- A natural isomorphism on K-flat representatives extends to derived bifunctors.
Source: Stacks Project, Cohomology, Tag 06YH and section-derived-pullback, the
localization argument of Tag 079U; Mathlib localization of bifunctors.
(blueprint: lem-pc-kflat-bifunctor-iso-descent).

Proof: take the full subcategory of K-flat cochain complexes. Its inclusion followed
by Q is a localization at quasi-isomorphisms: functorial flat resolutions give an
inverse on localized categories, with the resolution augmentations identifying both
composites with identities. The supplied simultaneous naturality gives a natural
isomorphism between the restrictions of U and V (use identity maps to get naturality
in each variable). Localize this isomorphism in both variables by lift₂NatIso.
Both restrictions have the tautological lifting isomorphism, so its components on
K-flat representatives are exactly the given components. The inverse descends by
the same construction. This argument requires no tensor, pullback or coherence
structure on U or V and includes the empty scheme. -/
theorem kFlat_bifunctor_iso_descent (X : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    {E : Type uE} [Category.{vE} E]
    (U V : schemeDerivedCategory X ⥤ schemeDerivedCategory X ⥤ E)
    (e : ∀ (P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ),
        CochainComplex.IsKFlatTensor (R := X.sheaf) P →
        CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((U.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N) ≅
          (V.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)))
    (he : ∀ (P P' N N' : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
        (hP' : CochainComplex.IsKFlatTensor (R := X.sheaf) P')
        (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N)
        (hN' : CochainComplex.IsKFlatTensor (R := X.sheaf) N') (a : P ⟶ P') (b : N ⟶ N'),
      (U.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj N) ≫
          (U.obj (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b) ≫
          (e P' N' hP' hN').hom =
        (e P N hP hN).hom ≫
          (V.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj N) ≫
          (V.obj (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map b)) :
    ∃ μ : U ≅ V, ∀ (P N : CochainComplex
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
      (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N),
      ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom =
        (e P N hP hN).hom := by
  classical
  let A := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} A :=
    Limits.hasColimitsOfSizeShrink.{0, 0, uModel, uModel} A
  have (M : A) : Limits.PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj M) :=
    Limits.preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let J : CochainComplex.KFlat A ⥤ schemeDerivedCategory X :=
    CochainComplex.ιKFlat A ⋙ DerivedCategory.Q
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence :=
    W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : J.IsLocalization W.WKFlat :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      W.localizerMorphismKFlat DerivedCategory.Q
  have toLean (P : CochainComplex.KFlat A) :
      CochainComplex.IsKFlatTensor (R := X.sheaf) P.obj := by
    have h := (HomotopyCategory.kFlat_quotient_obj_iff P.obj).2 P.property
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic] at h
    intro N hN
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      ((h ((HomotopyCategory.quotient A (.up ℤ)).obj N)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)).2)
  have fromLean (P : CochainComplex A ℤ)
      (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) : W.kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff]
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr : HomotopyCategory.subcategoryAcyclic A
        ((HomotopyCategory.quotient A (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient A (.up ℤ)).obj P) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic A).prop_of_iso (β_ _ _) hr, hr⟩
  let U₀ := (((Functor.whiskeringLeft₂ E).obj J).obj J).obj U
  let V₀ := (((Functor.whiskeringLeft₂ E).obj J).obj J).obj V
  let e₀ : U₀ ≅ V₀ := NatIso.ofComponents (fun P ↦ NatIso.ofComponents
    (fun N ↦ e P.obj N.obj (toLean P) (toLean N)) (by
      intro N N' b
      have h := he P.obj P.obj N.obj N'.obj
        (toLean P) (toLean P) (toLean N) (toLean N') (𝟙 _) b.hom
      simpa [U₀, V₀, J] using h)) (by
      intro P P' a
      ext N
      have h := he P.obj P'.obj N.obj N.obj
        (toLean P) (toLean P') (toLean N) (toLean N) a.hom (𝟙 _)
      simpa [U₀, V₀, J] using h)
  let : Localization.Lifting₂ J J W.WKFlat W.WKFlat U₀ U := ⟨Iso.refl _⟩
  let : Localization.Lifting₂ J J W.WKFlat W.WKFlat V₀ V := ⟨Iso.refl _⟩
  let μ := Localization.lift₂NatIso J J W.WKFlat W.WKFlat U₀ V₀ U V e₀
  refine ⟨μ, ?_⟩
  intro P N hP hN
  let P₀ : CochainComplex.KFlat A := ⟨P, fromLean P hP⟩
  let N₀ : CochainComplex.KFlat A := ⟨N, fromLean N hN⟩
  change ((μ.hom.app (J.obj P₀)).app (J.obj N₀)) = (e P N hP hN).hom
  simp only [μ, Localization.lift₂NatIso_hom, Localization.lift₂NatTrans_app_app]
  change (𝟙 _ ≫ (e P N hP hN).hom ≫ 𝟙 _) = (e P N hP hN).hom
  simp only [Category.id_comp, Category.comp_id]

end AlgebraicGeometry
