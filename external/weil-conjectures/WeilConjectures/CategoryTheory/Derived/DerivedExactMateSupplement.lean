/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedExactMate

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

/-- An ordinary transformation of exact functors, descended to unbounded derived categories.
Source: localization of the degreewise transformation
(blueprint: lem-pur-exact-derived-mate). -/
noncomputable def exactDerivedMap (α : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh)

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

end CategoryTheory.Adjunction
