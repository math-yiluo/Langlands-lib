/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Exact derived adjunctions and mates -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction
variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄] [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
private lemma homotopyMate (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') (K : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K =
      (adj'.mapHomotopyCategory (.up ℤ)).unit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app
            ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((G'.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C₄ (.up ℤ)).map _ =
    (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₄ (.up ℤ)).map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map, Functor.map_comp]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)

/-- The mate of an exact derived square is normalized by the ordinary mate on complexes.
Source: the mate calculation in Tag 0F1E; unbounded version of the argument in
`Adjunction.derivedPlus_mateEquiv_app_fac`.
(auxiliary; not a blueprint node).
Proof: expand the mate into a unit, the square, and a counit. Move the derived-functor
unit through these three factors using naturality. The defining unit and counit
factorizations of the unbounded derived adjunction reduce the expression to the
ordinary homotopy adjunction. On complexes that adjunction and its mates are computed
degree by degree, so it gives the mapped ordinary mate. -/
theorem derivedExact_mateEquiv_app_fac (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      G'.mapDerivedCategory)
    (hθ : ∀ N : HomotopyCategory C₂ (.up ℤ),
      θ.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N))
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app
          (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ) (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) := by
  have hmate : ∀ (Z : DerivedCategory C₁),
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).app Z =
        adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
            (G.mapDerivedCategory.obj (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (θ.app (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (G'.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app Z)) := fun Z => by
    simp [mateEquiv_apply]
  set N := (R.mapHomotopyCategory (.up ℤ)).obj K
  set u := R.rightDerivedFunctorUnit.app K
  have h₁ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map u)
  have h₂ := θ.naturality u
  have h₃ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  have h₄ := homotopyMate adj adj' σ K
  have h₅ := R'.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N ≫
      (G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K))
  have h₆ := (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C₄ (.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
      R'.rightDerivedFunctorUnit ((G.mapHomotopyCategory (.up ℤ)).obj N)
  have h₇ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategoryFactorsh.hom.app N)
  have h₈ := hθ N
  have h₉ := G'.mapDerivedCategoryFactorsh.hom.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₅ h₇ h₉
  rw [hmate, reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp (G'.mapDerivedCategory)]
  erw [h₃, h₄]
  erw [← Functor.map_comp (R'.mapHomotopyCategory (.up ℤ))]
  erw [Functor.map_comp DerivedCategory.Qh, Category.assoc, reassoc_of% h₅]
  erw [← reassoc_of% h₆, reassoc_of% h₇]
  congr 1
  have key : θ.app (DerivedCategory.Qh.obj N) ≫
      G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app N) ≫
        DerivedCategory.Qh.map
          ((G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) ≫
        G'.mapDerivedCategoryFactorsh.inv.app K := by
    rw [← cancel_mono (G'.mapDerivedCategoryFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    rw [h₉, reassoc_of% h₈]
    erw [Category.comp_id]
  rw [key]
  simp only [Functor.map_comp]
  simp only [Category.assoc]

end CategoryTheory.Adjunction
