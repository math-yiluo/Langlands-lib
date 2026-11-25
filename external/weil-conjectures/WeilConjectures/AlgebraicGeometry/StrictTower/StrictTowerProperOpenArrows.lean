/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-tower-proper-open-arrows).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

-- The right-derived construction agrees with exact localization, without imposing
-- a monoidal structure or a flat-resolution construction on a tower category.
@[irreducible] private noncomputable def exactAdj
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    R.rightDerivedFunctorIsoMapDerivedCategory

private theorem exactAdj_jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    exactAdj ((moduleJAdj B j).whiskerRight ℕᵒᵖ) = jAdj B j := by
  unfold exactAdj
  rfl

private theorem exactAdj_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (X : HomotopyCategory C (.up ℤ)) :
    (exactAdj a).unit.app (DerivedCategory.Qh.obj X) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  have h₁ := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit X
  have h₃ := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj X)
  have h₄ := R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app X)
  dsimp at h₁ h₃ h₄
  simp only [exactAdj, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% h₄]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃]
  erw [Iso.inv_hom_id_app, Category.comp_id]

-- Exact localization preserves mate equations for the specified unit normalization.
section ExactMates

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁)
  {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂} (adj₂ : f₂ ⊣ g₂)
  {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)
  (d₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
  (d₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
  (hu₁ : ∀ X : HomotopyCategory C₁ (.up ℤ),
    d₁.unit.app (DerivedCategory.Qh.obj X) ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₁.mapDerivedCategoryFactorsh.hom.app ((f₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X))
  (hu₂ : ∀ X : HomotopyCategory C₂ (.up ℤ),
    d₂.unit.app (DerivedCategory.Qh.obj X) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₂.mapDerivedCategoryFactorsh.hom.app ((f₂.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X))

include hu₁ hu₂ in
private theorem exact_mate_Qh
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C₁ (.up ℤ)) :
    d₂.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) =
      u.mapDerivedCategory.map
          (d₁.unit.app (DerivedCategory.Qh.obj X)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactorsh.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := d₂.unit.naturality
    (u.mapDerivedCategoryFactorsh.inv.app X)
  have h₂ := hu₂
    ((u.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₄
  have h₂' : d₂.unit.app
      (DerivedCategory.Qh.obj ((u.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactorsh.inv.app X ≫
      d₂.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X) ≫ (g₂.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := hu₁ X
  have k₁' : d₁.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactorsh.inv.naturality
    ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at k₂
  have hR : u.mapDerivedCategoryFactorsh.inv.app X ≫
      u.mapDerivedCategory.map
        (d₁.unit.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((u.mapHomotopyCategory (.up ℤ)).map
        ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hu₂ : (adj₂.mapHomotopyCategory (.up ℤ)).unit.app ((u.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj K)) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient _ adj₂ _
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient, hu₂]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app
      ((u.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (u.mapHomologicalComplex (.up ℤ)).map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C₂ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

include hu₁ hu₂ in
private theorem exact_mate
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    d₂.unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map (d₁.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C₁)) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      d₂.unit.app (u.mapDerivedCategory.obj K) =
      d₂.unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    d₂.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ d₁.unit.app K =
      d₁.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    d₁.unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (exact_mate_Qh adj₁ adj₂ τ β d₁ d₂ hu₁ hu₂ hβ _)]

end ExactMates

section EvaluationCoherence

private abbrev W {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :=
  (Functor.whiskeringRight ℕᵒᵖ C D).obj F

private instance W_limits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteLimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

private instance W_colimits {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteColimits (W F) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

private abbrev E (C : Type*) [Category C] (n : ℕ) :=
  (evaluation ℕᵒᵖ C).obj (op n)

variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ H)]
  (F G : C ⥤ D) (K : D ⥤ H)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
private noncomputable def evalD (n : ℕ) :
    (W F).mapDerivedCategory ⋙ (E D n).mapDerivedCategory ≅
      (E C n).mapDerivedCategory ⋙ F.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (W F) (E D n) ≪≫
    (Functor.mapDerivedCategoryCompIso (E C n) F).symm

private theorem evalD_nat (e : F ≅ G) (n : ℕ) :
    Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso ((Functor.whiskeringRight ℕᵒᵖ C D).mapIso e)).hom
        (E D n).mapDerivedCategory ≫ (evalD G n).hom =
      (evalD F n).hom ≫ Functor.whiskerLeft (E C n).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e).hom := by
  have h₁ := Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    ((Functor.whiskeringRight ℕᵒᵖ C D).mapIso e) (E D n)
  have h₂ := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft (E C n) e
  have he : Functor.isoWhiskerRight
      ((Functor.whiskeringRight ℕᵒᵖ C D).mapIso e) (E D n) =
      Functor.isoWhiskerLeft (E C n) e := rfl
  rw [he] at h₁
  dsimp only [evalD, Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (W F) (E D n)).inv]
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id_assoc]
  exact h₂

private theorem evalD_comp (n : ℕ) :
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso (W F) (W K)).inv
        (E H n).mapDerivedCategory ≫
      Functor.whiskerLeft (W F).mapDerivedCategory (evalD K n).hom ≫
      Functor.whiskerRight (evalD F n).hom K.mapDerivedCategory =
    (evalD (F ⋙ K) n).hom ≫ Functor.whiskerLeft (E C n).mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso F K).inv := by
  have h₁ := Functor.mapDerivedCategoryCompIso_assoc (W F) (W K) (E H n)
  simp only [W, Functor.whiskeringRight_obj_comp] at h₁
  have h₂ := Functor.mapDerivedCategoryCompIso_assoc (W F) (E D n) K
  have h₃ := Functor.mapDerivedCategoryCompIso_assoc (E C n) F K
  simp only [evalD, Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc]
  rw [← cancel_epi (Functor.mapDerivedCategoryCompIso (W (F ⋙ K)) (E H n)).inv]
  rw [← reassoc_of% h₁]
  simp only [← Functor.whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
  erw [reassoc_of% h₂]
  simp only [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id, Functor.whiskerRight_id',
    Category.id_comp]
  exact h₃.symm


@[irreducible] private noncomputable def towerSquare
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) : W F₁ ⋙ W F₂ ≅ W G₁ ⋙ W G₂ :=
  Functor.whiskeringRightObjCompIso F₁ F₂ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ C D).mapIso e ≪≫
    (Functor.whiskeringRightObjCompIso G₁ G₂).symm

private theorem towerSquare_eq
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    towerSquare F₁ F₂ G₁ G₂ e = (Functor.whiskeringRight ℕᵒᵖ C D).mapIso e := by
  apply Iso.ext
  ext M n
  simp [towerSquare, Functor.whiskeringRightObjCompIso]

private theorem towerSquare_hom_app
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : ℕᵒᵖ ⥤ C) (n : ℕᵒᵖ) :
    ((towerSquare F₁ F₂ G₁ G₂ e).hom.app K).app n = e.hom.app (K.obj n) := by
  simp [towerSquare, Functor.whiskeringRightObjCompIso]

private theorem towerSquare_symm
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    towerSquare G₁ G₂ F₁ F₂ e.symm = (towerSquare F₁ F₂ G₁ G₂ e).symm := by
  apply Iso.ext
  ext M n
  simp [towerSquare, Functor.whiskeringRightObjCompIso]

private theorem towerSquare_comp
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (L L' : C ⥤ D) (a : L ≅ F₁ ⋙ F₂) (b : L' ≅ G₁ ⋙ G₂) (h : L = L') :
    towerSquare F₁ F₂ G₁ G₂ (a.symm ≪≫ eqToIso h ≪≫ b) =
      ((Functor.whiskeringRight ℕᵒᵖ C D).mapIso a ≪≫
        Functor.whiskeringRightObjCompIso F₁ F₂).symm ≪≫
      eqToIso (congrArg (fun F : C ⥤ D ↦ W F) h) ≪≫
      ((Functor.whiskeringRight ℕᵒᵖ C D).mapIso b ≪≫
        Functor.whiskeringRightObjCompIso G₁ G₂) := by
  unfold towerSquare
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, eqToIso_map]
  apply Iso.ext
  ext M n
  simp [Functor.whiskeringRightObjCompIso]

private theorem evalD_square
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    [Abelian C] [Abelian A] [Abelian A'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory D] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ A')]
    [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (M : DerivedCategory (ℕᵒᵖ ⥤ C)) (n : ℕ) :
    (E D n).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (towerSquare F₁ F₂ G₁ G₂ e)).hom.app M) ≫
      (evalD G₂ n).hom.app ((W G₁).mapDerivedCategory.obj M) ≫
      G₂.mapDerivedCategory.map ((evalD G₁ n).hom.app M) =
    (evalD F₂ n).hom.app ((W F₁).mapDerivedCategory.obj M) ≫
      F₂.mapDerivedCategory.map ((evalD F₁ n).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app ((E C n).mapDerivedCategory.obj M) := by
  rw [towerSquare_eq]
  have hF := congrArg (fun t ↦ t.app M) (evalD_comp F₁ F₂ n)
  have hG := congrArg (fun t ↦ t.app M) (evalD_comp G₁ G₂ n)
  have he := congrArg (fun t ↦ t.app M) (evalD_nat (F₁ ⋙ F₂) (G₁ ⋙ G₂) e n)
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at *
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app] at hF hG he
  rw [← cancel_epi ((E D n).mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso (W F₁) (W F₂)).inv.app M))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    hG, reassoc_of% he, reassoc_of% hF]
  simp only [Iso.inv_hom_id_app_assoc]

end EvaluationCoherence
private theorem exact_mate_tower
    {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C₁)] [HasDerivedCategory (ℕᵒᵖ ⥤ D₁)]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C₂)] [HasDerivedCategory (ℕᵒᵖ ⥤ D₂)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D₁)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D₂)]
    {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (a₁ : f₁ ⊣ g₁)
    {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂} (a₂ : f₂ ⊣ g₂)
    {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
    [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
    [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
    [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
    [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)
    (hβ : ∀ K, a₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (a₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory (ℕᵒᵖ ⥤ C₁)) :
    (exactAdj (a₂.whiskerRight ℕᵒᵖ)).unit.app ((W u).mapDerivedCategory.obj K) ≫
        (W g₂).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (towerSquare u f₂ f₁ v β)).hom.app K) =
      (W u).mapDerivedCategory.map ((exactAdj (a₁.whiskerRight ℕᵒᵖ)).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (towerSquare g₁ u v g₂ τ)).hom.app
          ((W f₁).mapDerivedCategory.obj K) := by
  apply exact_mate (a₁.whiskerRight ℕᵒᵖ) (a₂.whiskerRight ℕᵒᵖ)
    (towerSquare g₁ u v g₂ τ) (towerSquare u f₂ f₁ v β)
    (exactAdj (a₁.whiskerRight ℕᵒᵖ)) (exactAdj (a₂.whiskerRight ℕᵒᵖ))
    (exactAdj_unit _) (exactAdj_unit _)
  intro M
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, W, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app, Adjunction.whiskerRight_unit_app_app]
  rw [towerSquare_hom_app, towerSquare_hom_app]
  exact hβ (M.obj n)


private theorem unit_iso_of_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (E : C ⥤ C') (S : D ⥤ D') (T : C' ⥤ D')
    [E.Full] [E.Faithful] [S.Faithful] [T.Full] [T.Faithful]
    (e : L ⋙ S ≅ E ⋙ T) : IsIso a.unit := by
  have : (L ⋙ S).Full := Functor.Full.of_iso e.symm
  have : (L ⋙ S).Faithful := Functor.Faithful.of_iso e.symm
  have : L.Full := Functor.Full.of_comp_faithful L S
  have : L.Faithful := Functor.Faithful.of_comp L S
  infer_instance

private theorem tower_unit_iso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) [IsIso a.unit] : IsIso (a.whiskerRight ℕᵒᵖ).unit := by
  have ht (M) : IsIso ((a.whiskerRight ℕᵒᵖ).unit.app M) := by
    dsimp only [Adjunction.whiskerRight]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem exact_unit_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] (d : L.mapDerivedCategory ⊣ R.mapDerivedCategory) :
    IsIso d.unit :=
  d.isIso_unit_of_iso (Functor.mapDerivedCategoryCompIso L R ≪≫
    Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
    Functor.mapDerivedCategoryIdIso C)

-- Scalar restriction identifies constant-ring modules with fixed-module sheaves.
private noncomputable def fixedPresheaf (X : Scheme.{u}) :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B) ⥤
      PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f :=
    { app := f.app
      naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }

private noncomputable def fixedRestriction (X : Scheme.{u}) :
    Modules B X ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (scalarUnit B X)).obj M.val
    let F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} B :=
      { obj := P.obj
        map := P.map
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp _ F
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app U := (ModuleCat.restrictScalars ((scalarUnit B X).app U).hom).map (f.val.app U)
      naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply f.val g x } }

private instance fixedRestriction_faithful (X : Scheme.{u}) :
    (fixedRestriction B X).Faithful where
  map_injective h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom) h) U) x

private instance scalarUnit_injective (X : Scheme.{u}) :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (scalarUnit B X) := by
  rw [← Presheaf.isLocallyInjective_forget_iff]
  change Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (forget CommRingCat.{u + 1}))
  infer_instance

private instance scalarUnit_surjective' (X : Scheme.{u}) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (scalarUnit B X) :=
  scalarUnit_surjective B X

set_option backward.isDefEq.respectTransparency false in
private instance fixedRestriction_full (X : Scheme.{u}) :
    (fixedRestriction B X).Full where
  map_surjective {M N} f := by
    let a : (PresheafOfModules.restrictScalars (scalarUnit B X)).obj M.val ⟶
        (PresheafOfModules.restrictScalars (scalarUnit B X)).obj N.val :=
      { app := f.hom.app
        naturality g := by ext x; exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let H := SheafOfModules.forget.{u + 1} R ⋙
      PresheafOfModules.restrictScalars.{u + 1} (scalarUnit B X)
    have : H.Full := inferInstance
    obtain ⟨b, hb⟩ := H.map_surjective a
    refine ⟨b, ?_⟩
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun t ↦ t.app U) hb) x

set_option backward.isDefEq.respectTransparency false in
private instance fixedRestriction_essSurj (X : Scheme.{u}) :
    (fixedRestriction B X).EssSurj where
  mem_essImage F := by
    let P := (fixedPresheaf B X).obj F.obj
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
    let M := (PresheafOfModules.sheafification.{u + 1} (R := R) (scalarUnit B X)).obj P
    let a := (PresheafOfModules.sheafificationAdjunction.{u + 1} (R := R)
      (scalarUnit B X)).unit.app P
    let f : F ⟶ (fixedRestriction B X).obj M :=
      ⟨{ app := a.app
         naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply a g x }⟩
    let H := sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
    have : IsIso (H.map f) := by
      have : IsIso ((sheafToPresheaf _ _).map (H.map f)) :=
        isIso_toSheafify _ (H.obj F).property
      exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
    have : IsIso f := isIso_of_reflects_iso _ H
    exact ⟨M, ⟨(asIso f).symm⟩⟩

private noncomputable def fixedEquivalence (X : Scheme.{u}) :
    Modules B X ≌ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) := by
  have : (fixedRestriction B X).IsEquivalence := {}
  exact (fixedRestriction B X).asEquivalence

private theorem sheaf_iso_of_bijective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F G : Sheaf J (ModuleCat.{u + 1} B)} (f : F ⟶ G)
    (h : ∀ U, Function.Bijective (f.hom.app U)) : IsIso f := by
  have hi (U) : IsIso (f.hom.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (h U)
  have : IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} B)).map f) := by
    change IsIso f.hom
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (sheafToPresheaf J (ModuleCat.{u + 1} B))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleDirectImage B f ⋙ fixedRestriction B Y ≅
      fixedRestriction B X ⋙ lowerStar (ModuleCat.{u + 1} B) f := by
  let a : moduleDirectImage B f ⋙ fixedRestriction B Y ⟶
      fixedRestriction B X ⋙ lowerStar (ModuleCat.{u + 1} B) f :=
    { app M :=
        ⟨{ app U := ModuleCat.homMk
            (M := ((fixedRestriction B Y).obj ((moduleDirectImage B f).obj M)).obj.obj U)
            (N := ((fixedRestriction B X).obj M).obj.obj
              ((Scheme.proEtaleBaseChange f).op.obj U)) (𝟙 _)
            (fun b ↦ by
              ext m
              exact (moduleDirectImage_scalarUnit B f M U b m).symm)
           naturality := by intros; ext; rfl }⟩
      naturality := by intros; ext; rfl }
  have hi (M) : IsIso (a.app M) :=
    sheaf_iso_of_bijective B (Scheme.ProEt.topology Y) (a.app M)
      (fun _ ↦ Function.bijective_id)
  have : IsIso a := NatIso.isIso_of_isIso_app _
  exact asIso a

private noncomputable def inverseSquare
    {A₁ A₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    (eA : A₁ ≌ A₂) (eC : C₁ ≌ C₂) (F : A₁ ⥤ C₁) (H : A₂ ⥤ C₂)
    (s : eA.functor ⋙ H ≅ F ⋙ eC.functor) : H ⋙ eC.inverse ≅ eA.inverse ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight eA.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eA.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s eC.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ eC.unitIso.symm ≪≫ Functor.rightUnitor _)

private noncomputable def leftAdjointSquare
    {A₁ A₂ C₁ C₂ : Type*} [Category A₁] [Category A₂] [Category C₁] [Category C₂]
    (eA : A₁ ≌ A₂) (eC : C₁ ≌ C₂) {F : A₁ ⥤ C₁} {R : C₁ ⥤ A₁}
    {H : A₂ ⥤ C₂} {S : C₂ ⥤ A₂} (a : F ⊣ R) (b : H ⊣ S)
    (s : R ⋙ eA.functor ≅ eC.functor ⋙ S) :
    F ⋙ eC.functor ≅ eA.functor ⋙ H :=
  ((a.comp eC.toAdjunction).ofNatIsoRight
    (inverseSquare eC eA R S s.symm).symm).leftAdjointUniq (eA.toAdjunction.comp b)

private noncomputable def cancelSquare
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (P : A ⥤ A') (Q : B ⥤ B') (R : C ⥤ C') (S : D ⥤ D')
    [S.Full] [S.Faithful]
    (F' : A' ⥤ B') (G' : B' ⥤ D') (H' : A' ⥤ C') (I' : C' ⥤ D')
    (f : F ⋙ Q ≅ P ⋙ F') (g : G ⋙ S ≅ Q ⋙ G')
    (h : H ⋙ R ≅ P ⋙ H') (i : I ⋙ S ≅ R ⋙ I')
    (e : F' ⋙ G' ≅ H' ⋙ I') : F ⋙ G ≅ H ⋙ I := by
  apply ((Functor.FullyFaithful.ofFullyFaithful S).whiskeringRight A).preimageIso
  exact Functor.associator F G S ≪≫ Functor.isoWhiskerLeft F g ≪≫
    (Functor.associator F Q G').symm ≪≫ Functor.isoWhiskerRight f G' ≪≫
    Functor.associator P F' G' ≪≫ Functor.isoWhiskerLeft P e ≪≫
    (Functor.associator P H' I').symm ≪≫ Functor.isoWhiskerRight h.symm I' ≪≫
    Functor.associator H R I' ≪≫ Functor.isoWhiskerLeft H i.symm ≪≫
    (Functor.associator H I S).symm

private noncomputable def cancelIso
    {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
    (F G : A ⥤ D) (P : A ⥤ A') (S : D ⥤ D') [S.Full] [S.Faithful]
    (F' G' : A' ⥤ D') (f : F ⋙ S ≅ P ⋙ F') (g : G ⋙ S ≅ P ⋙ G')
    (e : F' ≅ G') : F ≅ G :=
  ((Functor.FullyFaithful.ofFullyFaithful S).whiskeringRight A).preimageIso
    (f ≪≫ Functor.isoWhiskerLeft P e ≪≫ g.symm)

private noncomputable def fixedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⋙ fixedRestriction B X ≅
      fixedRestriction B Y ⋙ upperStar (ModuleCat.{u + 1} B) f :=
  leftAdjointSquare (fixedEquivalence B Y) (fixedEquivalence B X)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) (fixedDirect B f)

private noncomputable def fixedOpen {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    moduleJ B j ⋙ fixedRestriction B X ≅
      fixedRestriction B U ⋙ openImmersionLowerShriek (ModuleCat.{u + 1} B) j :=
  leftAdjointSquare (fixedEquivalence B U) (fixedEquivalence B X)
    (moduleJAdj B j) (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (fixedPull B j)

@[irreducible] private noncomputable def moduleOpenSquare {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback a j' j g) :
    moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j' := by
  exact cancelSquare (moduleJ B j) (modulePullback B g)
    (modulePullback B a) (moduleJ B j')
    (fixedRestriction B U) (fixedRestriction B X) (fixedRestriction B U')
    (fixedRestriction B X') (openImmersionLowerShriek (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} B) g) (upperStar (ModuleCat.{u + 1} B) a)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j')
    (fixedOpen B j) (fixedPull B g) (fixedPull B a) (fixedOpen B j')
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) hsq).symm

@[irreducible] private noncomputable def moduleClopenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : moduleJ B j ≅ moduleDirectImage B j := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} B) j j.isClosedEmbedding.isClosed_range
  exact cancelIso (moduleJ B j) (moduleDirectImage B j)
    (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j) (lowerStar (ModuleCat.{u + 1} B) j)
    (fixedOpen B j) (fixedDirect B j)
    (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j))

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def squareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    G B i ⋙ G B r ≅ G B p ⋙ G B k :=
  (gComp B r i).symm ≪≫ eqToIso (congrArg (G B) h.symm) ≪≫ gComp B k p

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Derived B U) :
    (J B j').obj ((G B gU).obj M) ⟶ (G B g).obj ((J B j).obj M) :=
  ((jAdj B j').homEquiv _ _).symm
    ((G B gU).map ((jAdj B j).unit.app M) ≫
      (squareG B gU j' j g h).inv.app ((J B j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem betaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Derived B U) (f : M ⟶ N) :
    (G B gU ⋙ J B j').map f ≫ betaInvApp B gU j' j g h N =
      betaInvApp B gU j' j g h M ≫ (J B j ⋙ G B g).map f := by
  apply (jAdj B j').homEquiv_naturality_right_square
  exact ((Functor.whiskerRight (jAdj B j).unit (G B gU)) ≫
    Functor.whiskerLeft (J B j) (squareG B gU j' j g h).inv).naturality f

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    G B gU ⋙ J B j' ⟶ J B j ⋙ G B g where
  app := betaInvApp B gU j' j g h
  naturality := betaInvApp_naturality B gU j' j g h

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso (moduleJAdj B j).unit :=
    unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
      (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
      (openImmersionLowerShriek A j) (fixedOpen B j)
  have : IsIso (((moduleJAdj B j).whiskerRight ℕᵒᵖ).unit) :=
    tower_unit_iso (moduleJAdj B j)
  exact exact_unit_iso (C := Towers B U) (D := Towers B X)
    (L := towerJ B j) (R := towerPullback B j)
    ((moduleJAdj B j).whiskerRight ℕᵒᵖ) (jAdj B j)

private theorem derived_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] {F G : C ⥤ D}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F = G) (hd : F.mapDerivedCategory = G.mapDerivedCategory) :
    (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom = (eqToIso hd).hom := by
  subst G
  simpa only [eqToIso_refl, Iso.refl_hom] using
    (Functor.mapDerivedCategoryNatIso_refl (F := F))

private theorem derivedSquare_comp
    {C A A' D : Type*} [Category C] [Category A] [Category A'] [Category D]
    [Abelian C] [Abelian A] [Abelian A'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory A']
    [HasDerivedCategory D]
    (F₁ : C ⥤ A) (F₂ : A ⥤ D) (G₁ : C ⥤ A') (G₂ : A' ⥤ D)
    (L L' : C ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (a : L ≅ F₁ ⋙ F₂) (b : L' ≅ G₁ ⋙ G₂) (h : L = L')
    (hd : L.mapDerivedCategory = L'.mapDerivedCategory) :
    (Functor.mapDerivedCategorySquareIso (a.symm ≪≫ eqToIso h ≪≫ b)).hom =
      ((Functor.mapDerivedCategoryNatIso a ≪≫
        (Functor.mapDerivedCategoryCompIso F₁ F₂).symm).symm ≪≫ eqToIso hd ≪≫
        (Functor.mapDerivedCategoryNatIso b ≪≫
          (Functor.mapDerivedCategoryCompIso G₁ G₂).symm)).hom := by
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [derived_eqToIso h hd]

private theorem towerSquare_moduleSquareG {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    towerSquare (modulePullback B i) (modulePullback B r)
      (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h) =
      (towerGComp B r i).symm ≪≫ eqToIso (congrArg (towerPullback B) h.symm) ≪≫
        towerGComp B k p := by
  rw [moduleSquareG_eq]
  exact towerSquare_comp (modulePullback B i) (modulePullback B r)
    (modulePullback B p) (modulePullback B k) (modulePullback B (r ≫ i))
    (modulePullback B (k ≫ p)) (moduleGComp B r i) (moduleGComp B k p)
    (congrArg (modulePullback B) h.symm)
private theorem squareG_lift {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    (squareG B k r p i h).hom =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B i) (F₂ := towerPullback B r)
        (G₁ := towerPullback B p) (G₂ := towerPullback B k)
        (towerSquare (modulePullback B i) (modulePullback B r)
          (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h))).hom := by
  have hd := derivedSquare_comp (C := Towers B T) (A := Towers B S)
    (A' := Towers B W) (D := Towers B V)
    (towerPullback B i) (towerPullback B r) (towerPullback B p) (towerPullback B k)
    (towerPullback B (r ≫ i)) (towerPullback B (k ≫ p))
    (towerGComp B r i) (towerGComp B k p)
    (congrArg (towerPullback B) h.symm) (congrArg (G B) h.symm)
  exact hd.symm.trans (congrArg
    (fun e : towerPullback B i ⋙ towerPullback B r ≅
        towerPullback B p ⋙ towerPullback B k ↦
      (Functor.mapDerivedCategorySquareIso (F₁ := towerPullback B i)
        (F₂ := towerPullback B r) (G₁ := towerPullback B p) (G₂ := towerPullback B k)
        e).hom) (towerSquare_moduleSquareG B k r p i h).symm)


@[irreducible] private noncomputable def derivedOpenSquare {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback gU j' j g) :
    J B j ⋙ G B g ≅ G B gU ⋙ J B j' := by
  exact Functor.mapDerivedCategorySquareIso
    (F₁ := towerJ B j) (F₂ := towerPullback B g)
    (G₁ := towerPullback B gU) (G₂ := towerJ B j')
    (towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B gU)
      (moduleJ B j') (moduleOpenSquare B gU j' j g hsq))

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary B. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transport ordinary open base change through the equivalence between constant-ring
modules and sheaves of fixed B-modules, then extend termwise and localize. Thus G_g J_j M
lies in the essential image of the fully faithful J_jprime. The specified transpose is
its invertible counit composed with J_jprime of the pulled-back invertible open unit. -/
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv B gU j' j g h) := by
  have := jAdj_unit_isIso B j
  have := jAdj_unit_isIso B j'
  let ff := (jAdj B j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let d := derivedOpenSquare B gU j' j g hsq
  have hi (M : Derived B U) : IsIso ((betaInv B gU j' j g h).app M) := by
    have hc : IsIso ((jAdj B j').counit.app ((G B g).obj ((J B j).obj M))) :=
      (jAdj B j').isIso_counit_app_of_iso (d.app M)
    have hu : IsIso ((jAdj B j).unit.app M) := inferInstance
    change IsIso (betaInvApp B gU j' j g h M)
    unfold betaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J B j ⋙ G B g ≅ G B gU ⋙ J B j' :=
  (@asIso _ _ _ _ (betaInv B gU j' j g h)
    (betaInv_isIso B gU j' j g h hsq)).symm

set_option backward.isDefEq.respectTransparency true in
private theorem betaInv_lift [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) :
    betaInv B a j' j g h =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B a) (F₂ := towerJ B j')
        (G₁ := towerJ B j) (G₂ := towerPullback B g)
        (towerSquare (modulePullback B a) (moduleJ B j') (moduleJ B j)
          (modulePullback B g) (@asIso _ _ _ _ (singleBetaInv B a j' j g h)
            (singleBetaInv_isIso B a j' j g h hsq)))).hom := by
  let e := @asIso _ _ _ _ (singleBetaInv B a j' j g h)
    (singleBetaInv_isIso B a j' j g h hsq)
  let w := towerSquare (modulePullback B g) (modulePullback B j')
    (modulePullback B j) (modulePullback B a) (moduleSquareG B a j' j g h)
  have hτ : (Functor.mapDerivedCategorySquareIso
      (F₁ := towerPullback B j) (F₂ := towerPullback B a)
      (G₁ := towerPullback B g) (G₂ := towerPullback B j') w.symm).hom =
      (squareG B a j' j g h).inv := by
    have he : squareG B a j' j g h = Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B g) (F₂ := towerPullback B j')
        (G₁ := towerPullback B j) (G₂ := towerPullback B a) w :=
      Iso.ext (squareG_lift B a j' j g h)
    rw [he]
    simp only [Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
  have hm (K : Modules B U) :
      (moduleJAdj B j').unit.app ((modulePullback B a).obj K) ≫
          (modulePullback B j').map (e.hom.app K) =
        (modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
          (moduleSquareG B a j' j g h).inv.app ((moduleJ B j).obj K) := by
    simpa only [e, asIso_hom, singleBetaInv, singleBetaInvApp,
      Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
      ((moduleJAdj B j').homEquiv ((modulePullback B a).obj K)
        ((modulePullback B g).obj ((moduleJ B j).obj K))).apply_symm_apply
        ((modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
          (moduleSquareG B a j' j g h).inv.app ((moduleJ B j).obj K))
  apply NatTrans.ext
  funext M
  apply ((jAdj B j').homEquiv ((G B a).obj M)
    ((G B g).obj ((J B j).obj M))).injective
  change (jAdj B j').homEquiv ((G B a).obj M) ((G B g).obj ((J B j).obj M))
    (betaInvApp B a j' j g h M) = _
  rw [betaInvApp, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  symm
  rw [← hτ, ← exactAdj_jAdj B j, ← exactAdj_jAdj B j']
  dsimp only [w]
  rw [← towerSquare_symm]
  exact exact_mate_tower (C₁ := Modules B U) (D₁ := Modules B X)
    (C₂ := Modules B U') (D₂ := Modules B X')
    (f₁ := moduleJ B j) (g₁ := modulePullback B j)
    (f₂ := moduleJ B j') (g₂ := modulePullback B j')
    (u := modulePullback B a) (v := modulePullback B g)
    (moduleJAdj B j) (moduleJAdj B j') (moduleSquareG B a j' j g h).symm e hm M

set_option backward.isDefEq.respectTransparency true in
private theorem singleBeta_lift [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) :
    singleBeta B a j' j g h hsq = Functor.mapDerivedCategorySquareIso
      (F₁ := moduleJ B j) (F₂ := modulePullback B g)
      (G₁ := modulePullback B a) (G₂ := moduleJ B j')
      (@asIso _ _ _ _ (singleBetaInv B a j' j g h)
        (singleBetaInv_isIso B a j' j g h hsq)).symm := rfl
private theorem evalJ_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : evalJ B j n = evalD (moduleJ B j) n := by
  apply Iso.ext
  change (Functor.mapDerivedCategoryCompIso (towerJ B j) (E (Modules B X) n) ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIso (E (Modules B U) n) (moduleJ B j)).symm).hom = _
  simp only [evalD, Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom,
    Iso.symm_hom, Category.id_comp]

private theorem evalG_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    evalG B f n = evalD (modulePullback B f) n := by
  apply Iso.ext
  change (Functor.mapDerivedCategoryCompIso (towerPullback B f) (E (Modules B X) n) ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIso (E (Modules B Y) n) (modulePullback B f)).symm).hom = _
  simp only [evalD, Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom,
    Iso.symm_hom, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
/-- Evaluation at finite constant coefficients gives exactly the dependency's
unit-normalized open base change. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transpose inverse comparisons under the open adjunction. Evaluation
commutes with termwise G and J, and evaluates their units to the ordinary units.
The two transposes are identical. Exact localization and the adjunction Hom
bijection give equality of these particular comparisons. -/
theorem beta_evaluation [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Derived B U) (n : ℕ) :
    (ev B X' n).map ((beta B a j' j g h hsq).hom.app M) ≫
        (evalJ B j' n).hom.app ((G B a).obj M) ≫
        (moduleJ B j').mapDerivedCategory.map ((evalG B a n).hom.app M) =
      (evalG B g n).hom.app ((J B j).obj M) ≫
        (modulePullback B g).mapDerivedCategory.map ((evalJ B j n).hom.app M) ≫
        (singleBeta B a j' j g h hsq).hom.app ((ev B U n).obj M) := by
  let e := @asIso _ _ _ _ (singleBetaInv B a j' j g h)
    (singleBetaInv_isIso B a j' j g h hsq)
  let de := Functor.mapDerivedCategorySquareIso
    (F₁ := towerPullback B a) (F₂ := towerJ B j')
    (G₁ := towerJ B j) (G₂ := towerPullback B g)
    (towerSquare (modulePullback B a) (moduleJ B j') (moduleJ B j)
      (modulePullback B g) e)
  have hb : beta B a j' j g h hsq = de.symm := by
    apply Iso.ext_inv
    exact betaInv_lift B a j' j g h hsq
  have hs : Functor.mapDerivedCategorySquareIso
      (F₁ := towerJ B j) (F₂ := towerPullback B g)
      (G₁ := towerPullback B a) (G₂ := towerJ B j')
      (towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B a)
        (moduleJ B j') e.symm) = de.symm := by
    rw [towerSquare_symm]
    apply Iso.ext
    simp only [de, Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
  have he := evalD_square (moduleJ B j) (modulePullback B g)
    (modulePullback B a) (moduleJ B j') e.symm M n
  rw [hs, ← hb] at he
  rw [← evalJ_eq B j n, ← evalJ_eq B j' n, ← evalG_eq B a n, ← evalG_eq B g n] at he
  rw [singleBeta_lift B a j' j g h hsq]
  exact he


/-- The map of a proper/open commutative square into its canonical fibre product.
Source: Stacks, Tag 0F7B and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable abbrev squareLift {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) := pullback.lift k r h

/-- The induced lift is open and closed; no cartesian or identity-left assumption.
Source: Stacks, Tags 01W6 and 01IQ, and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: identify the fibre product with p⁻¹(S), an open in W. The map s identifies V
with k(V) inside this open. The base change q of p is separated and q s = r is
proper, so the proper-over-separated theorem makes s proper. A proper open immersion
is closed. This includes the empty open and gives the complementary open component. -/
theorem squareLift_clopen {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    IsOpenImmersion (squareLift k r p i h) ∧ IsClosedImmersion (squareLift k r p i h) := by
  have hopen : IsOpenImmersion (squareLift k r p i h) := by
    have : IsOpenImmersion (squareLift k r p i h ≫ pullback.fst p i) := by
      simpa only [squareLift, pullback.lift_fst] using (inferInstance : IsOpenImmersion k)
    exact IsOpenImmersion.of_comp _ (pullback.fst p i)
  have hproper : IsProper (squareLift k r p i h) := by
    have : IsProper (squareLift k r p i h ≫ pullback.snd p i) := by
      simpa only [squareLift, pullback.lift_snd] using (inferInstance : IsProper r)
    exact IsProper.of_comp _ (pullback.snd p i)
  exact ⟨hopen, IsClosedImmersion.of_isPreimmersion _
    ((squareLift k r p i h).isClosedMap.isClosed_range)⟩

/-- Open part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_open {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsOpenImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).1

/-- Closed part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_closed {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsClosedImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).2

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def openToR {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J B j ⟶ R B j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (J B j) (adj B j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (jAdj B j).unit (jAdj_unit_isIso B j)) (R B j) ≫
          (Functor.leftUnitor _).hom

@[irreducible] private noncomputable def derivedClopenIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : J B j ≅ R B j := by
  let e : towerJ B j ≅ towerDirectImage B j :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleClopenIso B j)
  have : PreservesFiniteLimits (towerDirectImage B j) :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (towerDirectImage B j) :=
    preservesFiniteColimits_of_natIso e
  exact Functor.mapDerivedCategoryNatIso e ≪≫
    (towerDirectImage B j).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transport the ordinary clopen extension/direct-image isomorphism through the
constant-ring module equivalence. Termwise direct image is therefore exact, so its
right derived functor R is isomorphic to J and is fully faithful. The direct-image
adjunction unit is invertible on J M, which lies in the essential image of R. The
specified comparison is this unit followed by R of the inverse open unit. -/
theorem openToR_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToR B j) := by
  let d := derivedClopenIso B j
  have := jAdj_unit_isIso B j
  let ff := (jAdj B j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (R B j).Full := Functor.Full.of_iso d
  have : (R B j).Faithful := Functor.Faithful.of_iso d
  have hi (M : Derived B U) : IsIso ((openToR B j).app M) := by
    have hu : IsIso ((adj B j).unit.app ((J B j).obj M)) :=
      (adj B j).isIso_unit_app_of_iso (d.app M)
    have hv : IsIso ((inv (jAdj B j).unit).app M) := inferInstance
    have hw : IsIso ((R B j).map ((inv (jAdj B j).unit).app M)) := inferInstance
    dsimp only [openToR, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    exact IsIso.comp_isIso' hu (IsIso.comp_isIso' hw (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def pi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Derived B X) ⟶ G B s ⋙ J B s :=
  (adj B s).unit ≫ Functor.whiskerLeft (G B s)
    (@inv _ _ _ _ (openToR B s) (openToR_isIso B s))

/-- The normalized non-cartesian open comparison uses beta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J B i ⋙ G B p ⟶ G B r ⋙ J B k :=
  (beta B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (G B (pullback.snd p i))
    (pi B (squareLift k r p i h))) (J B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (G B (pullback.snd p i)) (G B (squareLift k r p i h))
      (J B (squareLift k r p i h))).inv (J B (pullback.fst p i)) ≫
  (Functor.associator (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    (J B (squareLift k r p i h)) (J B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    ((jComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (jCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((gComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (G B) (pullback.lift_snd k r h))).hom) (J B k)

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha.
Source: Stacks, Tags 0F7B and 07A7
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R B r ⋙ J B i ⟶ J B k ⋙ R B p :=
  mateEquiv (adj B r) (adj B p) (alpha B k r p i h)

/-- The base-change arrow is the mate of the canonical pullback-square isomorphism.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def exchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    R B p ⋙ G B i ⟶ G B k ⋙ R B r :=
  mateEquiv (adj B p) (adj B r) (squareG B k r p i h).hom

end AlgebraicGeometry.ProEtale.StrictTower
