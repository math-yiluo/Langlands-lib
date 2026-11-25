/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Cochain Hom normalization for an exact left adjoint

Source: Stacks 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CategoryTheory.Adjunction

/-- The native derived adjunction transposes cochain maps with its actual right-derived
unit. Source: Stacks 0FND and 09T5; Mathlib derivedη_fac_app.
Proof: apply derivedη_fac_app to the homotopy adjunction at the quotient of P.
The termwise adjunction unit and the exact functor localization factorization have
the stated cochain components; the quotient comparison has identity components.
Expand the Hom transpose as the derived unit followed by the derived right functor
of the given map. Substitute the unit equation and use naturality of the universal
right-derived unit at f. Functoriality combines the localized ordinary unit with
the ordinary right functor of f, giving exactly the ordinary Hom transpose.
No K-injectivity of K is needed, since the universal unit is never inverted.
(blueprint: lem-pur-exact-left-cochain-transpose). -/
theorem derivedCochain_transpose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex C ℤ) (K : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        G.rightDerivedFunctorUnitQ K := by
  let qP := (HomotopyCategory.quotient C (.up ℤ)).obj P
  let eC := DerivedCategory.quotientCompQhIso C
  let eD := DerivedCategory.quotientCompQhIso D
  let adj := a.mapDerivedCategoryRightDerivedAdjunction
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit qP
  change adj.unit.app (DerivedCategory.Qh.obj qP) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app qP) = _ at hu
  have h₁ : adj.unit.app (DerivedCategory.Q.obj P) =
      eC.inv.app P ≫ adj.unit.app (DerivedCategory.Qh.obj qP) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategory.map (eC.hom.app P)) := by
    rw [← cancel_epi (eC.hom.app P), Iso.hom_inv_id_app_assoc]
    exact adj.unit.naturality (eC.hom.app P)
  have h₂ : F.mapDerivedCategory.map (eC.hom.app P) ≫ F.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactorsh.hom.app qP ≫
        eD.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Category.assoc]
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  have hn := G.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map f)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hu
  rw [Adjunction.homEquiv_unit, h₁]
  simp only [Category.assoc]
  rw [← Functor.map_comp, reassoc_of% h₂, Functor.map_comp, ← Category.assoc (adj.unit.app _),
    hu]
  have h₃ : eD.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map f =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ eD.hom.app K :=
    (DerivedCategory.quotientCompQhIso_hom_naturality f).symm
  erw [h₃, Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hn]
  rw [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [← Functor.map_comp_assoc]
  congr 2
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map,
    ← Functor.map_comp]
  rfl

end CategoryTheory.Adjunction
