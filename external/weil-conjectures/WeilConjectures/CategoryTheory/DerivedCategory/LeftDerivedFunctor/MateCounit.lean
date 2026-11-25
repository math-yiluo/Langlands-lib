/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.HomotopyCategory.MateCounit

/-!
# Mates of derived functors along levelwise derived adjunctions

Let `adj₁ : E₁ ⊣ R₁` and `adj₂ : E₂ ⊣ R₂` be adjunctions between abelian categories with exact
right adjoints, `G`, `H` exact functors, `β : E₁ ⋙ H ≅ G ⋙ E₂` an isomorphism and
`e : R₁ ⋙ G ≅ H ⋙ R₂` an isomorphism whose hom is the mate of `β.inv`. Suppose given total left
derived functors `LE₁`, `LE₂`, `LG`, `LH` (through their counits), derived adjunctions
`LE₁ ⊣ D(R₁)` and `LE₂ ⊣ D(R₂)` whose counits are induced by those of `adj₁` and `adj₂`, and an
isomorphism `LE₁ ⋙ LH ≅ LG ⋙ LE₂` induced by `β`. Then the mate of that isomorphism is the
isomorphism `D(R₁) ⋙ LG ≅ LH ⋙ D(R₂)` induced by `e`
(`CategoryTheory.Adjunction.mateEquiv_leftDerived_inv_eq`).

All the data are arbitrary, so that the kernel checks these diagram chases once, without
unfolding the concrete categories and functors they are applied to.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {A₁ A₂ B₁ B₂ : Type*} [Category* A₁] [Category* A₂] [Category* B₁] [Category* B₂]
  [Abelian A₁] [Abelian A₂] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  {R₁ : A₁ ⥤ B₁} {R₂ : A₂ ⥤ B₂} {G : B₁ ⥤ B₂} {H : A₁ ⥤ A₂}
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {LG : DerivedCategory B₁ ⥤ DerivedCategory B₂} {LH : DerivedCategory A₁ ⥤ DerivedCategory A₂}

namespace Functor

/-- Let `Γ : D(R₁) ⋙ LG ≅ LH ⋙ D(R₂)` be induced by an isomorphism `e : R₁ ⋙ G ≅ H ⋙ R₂` of
exact functors, through identifications `ιG : LG ≅ D(G)` and `ιH : LH ≅ D(H)` compatible with the
counits `cG` and `cH`. On the image of an object of the homotopy category, `Γ` is induced,
through these counits, by `e` on homotopy categories. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj_comp_counit
    (cG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιG : LG ≅ G.mapDerivedCategory)
    (hιG : ∀ K, ιG.hom.app (DerivedCategory.Qh.obj K) ≫ G.mapDerivedCategoryFactorsh.hom.app K =
      cG.app K)
    (cH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιH : LH ≅ H.mapDerivedCategory)
    (hιH : ∀ K, ιH.hom.app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategoryFactorsh.hom.app K =
      cH.app K)
    (e : R₁ ⋙ G ≅ H ⋙ R₂) (Γ : R₁.mapDerivedCategory ⋙ LG ≅ LH ⋙ R₂.mapDerivedCategory)
    (hΓ : Γ = isoWhiskerLeft R₁.mapDerivedCategory ιG ≪≫ mapDerivedCategorySquareIso e ≪≫
      isoWhiskerRight ιH.symm R₂.mapDerivedCategory)
    (K : HomotopyCategory A₁ (.up ℤ)) :
    Γ.hom.app (DerivedCategory.Qh.obj K) ≫ R₂.mapDerivedCategory.map (cH.app K) ≫
        R₂.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj K) =
      LG.map (R₁.mapDerivedCategoryFactorsh.hom.app K) ≫
        cG.app ((R₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K ≫
          (mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) := by
  subst hΓ
  have hsq := mapDerivedCategorySquareIso_hom_app_Qh_obj e K
  have hn := ιG.hom.naturality (R₁.mapDerivedCategoryFactorsh.hom.app K)
  have hS : ιH.inv.app (DerivedCategory.Qh.obj K) ≫ cH.app K =
      H.mapDerivedCategoryFactorsh.hom.app K := by
    rw [← hιH, Iso.inv_hom_id_app_assoc]
  have hsq' : (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj K) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app K) ≫
      R₂.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (R₁.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((R₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K ≫
        (mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) := by
    rw [← hsq]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
  generalize mapDerivedCategorySquareIso e = s at hsq' ⊢
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp_assoc, hS]
  rw [hsq', ← hιG, ← reassoc_of% hn, Category.assoc]

end Functor

namespace Adjunction

variable [(HomotopyCategory.quotient A₁ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A₁ (.up ℤ))]
  [(HomotopyCategory.quotient A₂ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A₂ (.up ℤ))]
  [(HomotopyCategory.quotient B₁ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B₁ (.up ℤ))]
  [(HomotopyCategory.quotient B₂ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B₂ (.up ℤ))]
  {E₁ : B₁ ⥤ A₁} {E₂ : B₂ ⥤ A₂} [E₁.Additive] [E₂.Additive]
  {LE₁ : DerivedCategory B₁ ⥤ DerivedCategory A₁} {LE₂ : DerivedCategory B₂ ⥤ DerivedCategory A₂}

/-- Mates of derived functors: the mate, along derived adjunctions `LE₁ ⊣ D(R₁)` and
`LE₂ ⊣ D(R₂)` whose counits are induced by those of `adj₁ : E₁ ⊣ R₁` and `adj₂ : E₂ ⊣ R₂`, of
an isomorphism `LE₁ ⋙ LH ≅ LG ⋙ LE₂` induced by `β : E₁ ⋙ H ≅ G ⋙ E₂` is the isomorphism
`D(R₁) ⋙ LG ≅ LH ⋙ D(R₂)` induced by the mate `e : R₁ ⋙ G ≅ H ⋙ R₂` of `β.inv`. -/
theorem mateEquiv_leftDerived_inv_eq (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (β : E₁ ⋙ H ≅ G ⋙ E₂) (e : R₁ ⋙ G ≅ H ⋙ R₂) (he : mateEquiv adj₁ adj₂ β.inv = e.hom)
    (βh : E₁.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ≅
      G.mapHomotopyCategory (.up ℤ) ⋙ E₂.mapHomotopyCategory (.up ℤ))
    (hβh : βh.inv = ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ E₂)) (.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory β.inv (.up ℤ)) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (E₁ ⋙ H)) (.up ℤ)).inv)
    (cE₁ : DerivedCategory.Qh ⋙ LE₁ ⟶ E₁.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cE₂ : DerivedCategory.Qh ⋙ LE₂ ⟶ E₂.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιG : LG ≅ G.mapDerivedCategory)
    (hιG : ∀ K, ιG.hom.app (DerivedCategory.Qh.obj K) ≫ G.mapDerivedCategoryFactorsh.hom.app K =
      cG.app K)
    (cH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιH : LH ≅ H.mapDerivedCategory)
    (hιH : ∀ K, ιH.hom.app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategoryFactorsh.hom.app K =
      cH.app K)
    (dadj₁ : LE₁ ⊣ R₁.mapDerivedCategory) (dadj₂ : LE₂ ⊣ R₂.mapDerivedCategory)
    (hε₁ : ∀ K, dadj₁.counit.app (DerivedCategory.Qh.obj K) =
      LE₁.map (R₁.mapDerivedCategoryFactorsh.hom.app K) ≫
        cE₁.app ((R₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).counit.app K))
    (hε₂ : ∀ K, dadj₂.counit.app (DerivedCategory.Qh.obj K) =
      LE₂.map (R₂.mapDerivedCategoryFactorsh.hom.app K) ≫
        cE₂.app ((R₂.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).counit.app K))
    (Lβ : LE₁ ⋙ LH ≅ LG ⋙ LE₂)
    (κ₁ : DerivedCategory.Qh ⋙ LE₁ ⋙ LH ⟶
      E₁.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hκ₁ : κ₁ = Functor.whiskerRight cE₁ LH ≫
      Functor.whiskerLeft (E₁.mapHomotopyCategory (.up ℤ)) cH)
    (κ₂ : DerivedCategory.Qh ⋙ LG ⋙ LE₂ ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ E₂.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hκ₂ : κ₂ = Functor.whiskerRight cG LE₂ ≫
      Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) cE₂)
    (hLβ : ∀ K, Lβ.inv.app (DerivedCategory.Qh.obj K) ≫ κ₁.app K =
      κ₂.app K ≫ DerivedCategory.Qh.map (βh.inv.app K))
    (Γ : R₁.mapDerivedCategory ⋙ LG ≅ LH ⋙ R₂.mapDerivedCategory)
    (hΓ : Γ = Functor.isoWhiskerLeft R₁.mapDerivedCategory ιG ≪≫
      Functor.mapDerivedCategorySquareIso e ≪≫
        Functor.isoWhiskerRight ιH.symm R₂.mapDerivedCategory) :
    mateEquiv dadj₁ dadj₂ Lβ.inv = Γ.hom := by
  subst hκ₁ hκ₂
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (.up ℤ))
  intro K
  apply (dadj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have : IsIso (cH.app K) := by
    rw [← hιH]
    infer_instance
  rw [← cancel_mono (cH.app K)]
  have hm := mateEquiv_counit dadj₁ dadj₂ Lβ.inv (DerivedCategory.Qh.obj K)
  have hΓK := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp_counit cG ιG hιG cH ιH hιH
    e Γ hΓ K
  have hH := mapHomotopyCategory_map_comp_counit_app (.up ℤ) adj₁ adj₂ β e.hom he βh hβh K
  have hκ := cE₂.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K)
  have hβ := Lβ.inv.naturality (R₁.mapDerivedCategoryFactorsh.hom.app K)
  have hl := cH.naturality ((adj₁.mapHomotopyCategory (.up ℤ)).counit.app K)
  have hB := hLβ ((R₁.mapHomotopyCategory (.up ℤ)).obj K)
  rw [hm]
  simp only [Category.assoc]
  erw [← dadj₂.counit_naturality (cH.app K)]
  rw [hε₁]
  erw [hε₂ ((H.mapHomotopyCategory (.up ℤ)).obj K)]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hB
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hκ hβ hl
  simp only [← Functor.map_comp_assoc]
  rw [hΓK]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hβ, cancel_epi]
  simp only [Functor.map_comp, Category.assoc] at hκ
  rw [hl, reassoc_of% hB, reassoc_of% hκ]
  have hH' := congrArg DerivedCategory.Qh.map hH
  simp only [Functor.map_comp, Category.assoc] at hH' ⊢
  rw [hH']

end Adjunction

end CategoryTheory
