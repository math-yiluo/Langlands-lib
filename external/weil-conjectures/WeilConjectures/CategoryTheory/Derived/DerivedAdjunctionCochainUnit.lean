/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# Cochain normalization of the canonical derived adjunction unit

Source: Stacks Project, derived.tex, Tags 0DVC and 09T5.
(blueprint: lem-sfb-derived-adjunction-cochain-unit).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For an exact additive left adjoint, the canonical derived unit agrees with the
ordinary cochain unit followed by the universal right-derived comparison.
Source: Stacks Project, derived.tex, Tags 0DVC and 09T5.
(blueprint: lem-sfb-derived-adjunction-cochain-unit).
Proof: apply the normalized derived-unit equation on the homotopy category to the
quotient of E. The exact-functor factorization there is the cochain factorization
conjugated by quotientCompQhIso. Naturality of the derived unit transports its
source along that isomorphism; the inverse-hom identities cancel the intermediate
comparison. The remaining composite is precisely rightDerivedFunctorUnitQ. -/
theorem derived_unit_cochain
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {F : D ⥤ C} [L.Additive] [F.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (E : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj E) ≫
        F.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app E) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app E) ≫
        F.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj E) := by
  let M := (HomotopyCategory.quotient C (.up ℤ)).obj E
  let a := adj.mapDerivedCategoryRightDerivedAdjunction
  have hu := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit M
  have hq : DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app E) =
      𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [L.mapDerivedCategoryFactorsh_hom_app, hq] at hu
  erw [Category.comp_id] at hu
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app E)).mp
  have hn := a.unit.naturality ((DerivedCategory.quotientCompQhIso C).hom.app E)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  have hu' := congrArg (fun z ↦ z ≫ F.rightDerivedFunctor.map
    ((DerivedCategory.quotientCompQhIso D).hom.app
      ((L.mapHomologicalComplex (.up ℤ)).obj E))) hu
  simp only [Functor.map_comp, Category.assoc] at hu'
  rw [← F.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app] at hu'
  erw [F.rightDerivedFunctor.map_id, Category.comp_id] at hu'
  simp only [Functor.map_comp]
  erw [hu']
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  dsimp only [Functor.rightDerivedFunctorUnitQ]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Iso.hom_inv_id_app_assoc]
  rfl

end CategoryTheory
