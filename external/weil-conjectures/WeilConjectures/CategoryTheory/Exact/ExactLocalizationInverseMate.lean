/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Exact localization and inverse mates

Source: Stacks Project, Tag 07A7 (remark-base-change), and the inverse-mate
compatibility sentence of `fix-prop-coherence`.
(blueprint: lem-sf-exact-localization-inverse-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The exact adjunction obtained by localizing a specified termwise adjunction,
with independent universes on its two abelian categories. This item helper uses
the same construction as `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`;
when the universes agree, the two definitions are definitionally equal. Source: Stacks Tag 015F
(blueprint: lem-sf-exact-localization-inverse-mate). -/
def exactLocalizationDerivedAdjunction
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors F).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors G).symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

/-- The localized unit, using the specified exact-functor factorizations. -/
private lemma exact_unit_app
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) :
    (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app _ ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  unfold exactLocalizationDerivedAdjunction
  rw [Adjunction.localization_unit_app]
  rfl

/-- The localized Hom bijection agrees with the cochain Hom bijection. -/
private lemma exact_hom_fac
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    (exactLocalizationDerivedAdjunction a).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj N)
        (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R.mapDerivedCategoryFactors.inv.app N := by
  rw [Adjunction.homEquiv_unit, exact_unit_app, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp]
  exact congrArg
    (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫ ·)
    (R.mapDerivedCategoryFactors.inv.naturality f).symm

set_option backward.defeqAttrib.useBackward true in
/-- The standard derived square, conjugated by its cochain factorizations. -/
private lemma square_fac
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} C] [HasDerivedCategory.{w₄} D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex A ℤ) :
    F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app K) := by
  have hF := Functor.mapDerivedCategoryCompIso_fac F₁ F₂ K
  have hG := Functor.mapDerivedCategoryCompIso_fac G₁ G₂ K
  have he := Functor.mapDerivedCategoryNatIso_fac e K
  have hG' : (Functor.mapDerivedCategoryCompIso G₁ G₂).inv.app (DerivedCategory.Q.obj K) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app K) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hF' : F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K) ≫
        (F₁ ⋙ F₂).mapDerivedCategoryFactors.inv.app K := by
    rw [← cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hF, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/-- Localization preserves the unit equation characterizing a pair of mates. -/
private lemma mate_unit_Q
    {A : Type u₁} {B : Type u₂} {D : Type u₃} {F : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D] [Category.{v₄} F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} D] [HasDerivedCategory.{w₄} F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hβ : ∀ K, a₂.unit.app (G.obj K) ≫ R₂.map (β.hom.app K) =
      G.map (a₁.unit.app K) ≫ d.hom.app (L₁.obj K))
    (K : CochainComplex A ℤ) :
    (exactLocalizationDerivedAdjunction a₂).unit.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        R₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Q.obj K)) =
      G.mapDerivedCategory.map
          ((exactLocalizationDerivedAdjunction a₁).unit.app (DerivedCategory.Q.obj K)) ≫
        (Functor.mapDerivedCategorySquareIso d).hom.app
          (L₁.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  -- Reduce to a computation on cochain complexes.
  rw [← cancel_epi (G.mapDerivedCategoryFactors.inv.app K),
    ← cancel_mono (R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
      (L₁.mapDerivedCategoryFactors.hom.app K)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R₂.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj K)))]
  -- the left hand side
  have h₁ := (exactLocalizationDerivedAdjunction a₂).unit.naturality
    (G.mapDerivedCategoryFactors.inv.app K)
  have h₃ := square_fac β K
  have h₄ := R₂.mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L₂)) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ H)) (.up ℤ)).inv.app K)
  dsimp at h₁ h₄
  have h₂' := exact_unit_app a₂ ((G.mapHomologicalComplex (.up ℤ)).obj K)
  have h₃' := congrArg R₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : G.mapDerivedCategoryFactors.inv.app K ≫
      (exactLocalizationDerivedAdjunction a₂).unit.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      R₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Q.obj K)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
        (L₁.mapDerivedCategoryFactors.hom.app K)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R₂.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((a₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫ (R₂.mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L₂)) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ H)) (.up ℤ)).inv.app K)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁' := exact_unit_app a₁ K
  have k₂ := G.mapDerivedCategoryFactors.inv.naturality
    ((a₁.mapHomologicalComplex (.up ℤ)).unit.app K)
  have k₃ : G.mapDerivedCategory.map (R₁.mapDerivedCategory.map
      (L₁.mapDerivedCategoryFactors.inv.app K)) ≫
      (Functor.mapDerivedCategorySquareIso d).hom.app
        (L₁.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      (Functor.mapDerivedCategorySquareIso d).hom.app _ ≫
        R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
          (L₁.mapDerivedCategoryFactors.inv.app K)) :=
    (Functor.mapDerivedCategorySquareIso d).hom.naturality _
  have k₄ := square_fac d
    ((L₁.mapHomologicalComplex (.up ℤ)).obj K)
  dsimp at k₂
  have hR : G.mapDerivedCategoryFactors.inv.app K ≫
      G.mapDerivedCategory.map
        ((exactLocalizationDerivedAdjunction a₁).unit.app (DerivedCategory.Q.obj K)) ≫
      (Functor.mapDerivedCategorySquareIso d).hom.app
        (L₁.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
        (L₁.mapDerivedCategoryFactors.hom.app K)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R₂.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map
        ((a₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (R₁ ⋙ G)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ R₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
        (L₁.mapDerivedCategoryFactors.inv.app K)) ≫
        R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
          (L₁.mapDerivedCategoryFactors.hom.app K)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  have hc : (a₂.mapHomologicalComplex (.up ℤ)).unit.app
      ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (R₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ L₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (L₁ ⋙ H)) (.up ℤ)).inv.app K) =
      (G.mapHomologicalComplex (.up ℤ)).map ((a₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (R₁ ⋙ G)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ R₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  exact hc

/-- Exact localization preserves the inverse mate and its normalized Hom bijections.
Source: Stacks Project, Tag 07A7 (remark-base-change), and the inverse-mate
compatibility sentence of `fix-prop-coherence`.
(blueprint: lem-sf-exact-localization-inverse-mate).

Proof: localize the cochain unit with the specified exact-functor factorizations.
Expanding the localized Hom bijection and using naturality proves both Hom
normalizations. Characterize the inverse mate β by the unit equation
`η₂ ≫ R₂(β) = G(η₁) ≫ d`. The standard composition and transformation
factorizations show that its derived square satisfies the same equation on QK:
cancel the factorization isomorphisms and check the resulting cochain equality
degreewise. Injectivity of the second adjunction's Hom bijection identifies it
with the localized inverse mate on QK. Localization's natural-transformation
extensionality extends this equality to all objects. The derived square of β
is an isomorphism, giving the required invertibility. No faithfulness of Q is used. -/
theorem exact_localization_inverse_mate
    {A : Type u₁} {B : Type u₂} {D : Type u₃} {F : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D] [Category.{v₄} F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} D] [HasDerivedCategory.{w₄} F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    [IsIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom))] :
    IsIso ((mateEquiv
      (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) ∧
    ((mateEquiv
      (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) =
      (Functor.mapDerivedCategorySquareIso
        (asIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)))).hom ∧
    (∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
      (f : (L₁.mapHomologicalComplex (.up ℤ)).obj K ⟶ L),
      (exactLocalizationDerivedAdjunction a₁).homEquiv
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (L₁.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₁.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R₁.mapDerivedCategoryFactors.inv.app L) ∧
    (∀ (K : CochainComplex D ℤ) (L : CochainComplex F ℤ)
      (f : (L₂.mapHomologicalComplex (.up ℤ)).obj K ⟶ L),
      (exactLocalizationDerivedAdjunction a₂).homEquiv
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (L₂.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₂.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R₂.mapDerivedCategoryFactors.inv.app L) := by
  let β := asIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom))
  have hβ : ∀ K, a₂.unit.app (G.obj K) ≫ R₂.map (β.hom.app K) =
      G.map (a₁.unit.app K) ≫ d.hom.app (L₁.obj K) := fun K =>
    (unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ d.hom) K).symm
  have heq : ((mateEquiv
      (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) =
      (Functor.mapDerivedCategorySquareIso β).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    apply ((exactLocalizationDerivedAdjunction a₂).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm
      (exactLocalizationDerivedAdjunction a₁)
      (exactLocalizationDerivedAdjunction a₂)
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)
      (DerivedCategory.Q.obj K)).symm.trans (mate_unit_Q a₁ a₂ d β hβ K).symm
  refine ⟨?_, heq, exact_hom_fac a₁, exact_hom_fac a₂⟩
  rw [heq]
  infer_instance

end CategoryTheory
