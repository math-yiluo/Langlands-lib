/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenModuleIdentity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization

/-! # Identity normalization for ordinary open exchange

## References

* Stacks Project, Tags 03DI, 07A7 and 099N
-/



@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.OrdinaryOpenExchangeIdentity

theorem idFactors
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have h₁ : ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := rfl
  have h₃ : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [h₁, h₂, h₃] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at h
  exact h

theorem identityCounit
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F = G) (L : DerivedCategory C ⥤ DerivedCategory C)
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory)
    (he : Functor.ExactDerivedCounitNormalization F G L ε hp e)
    (n : G ≅ 𝟭 C) (P : CochainComplex C ℤ) :
    (e ≪≫ Functor.mapDerivedCategoryNatIso n ≪≫
        Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      ε P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (eqToIso h ≪≫ n).hom (.up ℤ)).app P) := by
  cases h
  have hn := he P
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, idFactors]
  rw [Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc, hn]
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

end AlgebraicGeometry.Scheme.OrdinaryOpenExchangeIdentity

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] cbcDatumOrdinaryTransport AdicCoefficientDatum.pullId
  cbcModulePullId cbcOpenShriek cbcUnderivedInverseExchange cbcDerivedInverseExchange

attribute [local irreducible] cbcOrdinaryExchange
  cbcDatumOrdinaryExchange

end AlgebraicGeometry.Scheme
-- Only imports remain after declaration-level pruning.
