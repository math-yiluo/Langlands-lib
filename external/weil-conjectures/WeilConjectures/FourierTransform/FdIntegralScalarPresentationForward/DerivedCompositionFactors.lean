/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Localization factors of a derived composition comparison

A generic form of the factorization of the derived composition comparison through the
localization factors, with every functor, factor and comparison passed as a variable together
with its defining equation. Instantiating it at a goal fixes all instance arguments to those of
the goal, so no kernel conversion between different instance paths is needed.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.FdIntegralScalarForward

/-- The derived composition comparison `D(F) ⋙ D(G) ≅ D(H)` induced by `F ⋙ G ≅ H₀` and an
equality `H₀ = H`, composed with the localization factor of `H`, factors through the localization
factors of `F` and `G` and the comparison of the cochain functors. -/
theorem derived_comp_factors
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [aC₁ : Abelian C₁] [aC₂ : Abelian C₂] [aC₃ : Abelian C₃]
    [dC₁ : HasDerivedCategory C₁] [dC₂ : HasDerivedCategory C₂] [dC₃ : HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H₀ H : C₁ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H₀.Additive] [PreservesFiniteLimits H₀] [PreservesFiniteColimits H₀]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (Oh : DerivedCategory C₁ ⥤ DerivedCategory C₂) (Ok : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (Ohk : DerivedCategory C₁ ⥤ DerivedCategory C₃)
    (hOh : Oh = F.mapDerivedCategory) (hOk : Ok = G.mapDerivedCategory)
    (hOhk : Ohk = H.mapDerivedCategory)
    (oh : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ)
    (ok : CochainComplex C₂ ℤ ⥤ CochainComplex C₃ ℤ)
    (ohk : CochainComplex C₁ ℤ ⥤ CochainComplex C₃ ℤ)
    (hoh : oh = F.mapHomologicalComplex (.up ℤ)) (hok : ok = G.mapHomologicalComplex (.up ℤ))
    (hohk : ohk = H.mapHomologicalComplex (.up ℤ))
    (foh : DerivedCategory.Q ⋙ Oh ≅ oh ⋙ DerivedCategory.Q)
    (fok : DerivedCategory.Q ⋙ Ok ≅ ok ⋙ DerivedCategory.Q)
    (fohk : DerivedCategory.Q ⋙ Ohk ≅ ohk ⋙ DerivedCategory.Q)
    (hfoh : foh ≍ F.mapDerivedCategoryFactors) (hfok : fok ≍ G.mapDerivedCategoryFactors)
    (hfohk : fohk ≍ H.mapDerivedCategoryFactors)
    (e₀ : F ⋙ G ≅ H₀) (hH : H₀ = H) (e : F ⋙ G ≅ H) (he : e = e₀ ≪≫ eqToIso hH)
    (oc : oh ⋙ ok ≅ ohk) (hoc : oc ≍ Functor.mapHomologicalComplexCompIso e (.up ℤ))
    (hd : H₀.mapDerivedCategory = Ohk) (Oc : Oh ⋙ Ok ≅ Ohk)
    (hOc : Oc ≍ (F.mapDerivedCategoryCompIso G ≪≫
      Functor.mapDerivedCategoryNatIso e₀) ≪≫ eqToIso hd)
    (P : CochainComplex C₁ ℤ) :
    Oc.hom.app (DerivedCategory.Q.obj P) ≫ fohk.hom.app P =
      Ok.map (foh.hom.app P) ≫ fok.hom.app (oh.obj P) ≫
        DerivedCategory.Q.map (oc.hom.app P) := by
  subst hOh hOk hOhk hoh hok hohk hH
  subst he
  obtain rfl := eq_of_heq hfoh
  obtain rfl := eq_of_heq hfok
  obtain rfl := eq_of_heq hfohk
  obtain rfl := eq_of_heq hoc
  obtain rfl := eq_of_heq hOc
  simp only [eqToIso_refl, Iso.trans_refl]
  rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  have hc := Functor.mapDerivedCategoryCompIso_hom_app_factors F G P
  rw [← Category.assoc, ← hc, Iso.hom_inv_id_app_assoc]
  simp only [Category.assoc]
  rfl

end WeilConjectures.FdIntegralScalarForward
