/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleShortExact
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompLevelwise

/-!
# The transition maps between reductions modulo `kₙ`

Let `φ' : R ⟶ S'`, `ψ : S' ⟶ S` and `φ : R ⟶ S` be morphisms of commutative algebra objects with
`φ' ≫ ψ = φ`; the case of interest is `S' = R/ℓⁿ⁺², S = R/ℓⁿ⁺¹`. This file constructs the
*transition* between the reductions `T' = L(Ext_φ') ⋙ D(Res_φ')` and `T = L(Ext_φ) ⋙ D(Res_φ)`,
```
t : S' ⊗ᴸ_R K ⟶ S ⊗ᴸ_R K,
```
a natural transformation `T' ⟶ T` (`Mod.derivedReductionTransition`). It is `D(Res_φ')` of the
map `τ : S' ⊗ᴸ_R K ⟶ D(Res_ψ)(S ⊗ᴸ_R K)` given by the unit of `L(Ext_ψ) ⊣ D(Res_ψ)` and the
transitivity isomorphism `S ⊗ᴸ_R K ≅ S ⊗ᴸ_{S'} (S' ⊗ᴸ_R K)` (`Mod.derivedExtendScalarsTransition`).

## Main results

- `Mod.unit_app_comp_derivedReductionTransition_app`: `t` is compatible with the units,
  `η'_K ≫ t_K = η_K`.
- `Mod.comp_derivedExtendScalarsTransition_app`: for a morphism `s : S' ⊗ᴸ_R B ⟶ S' ⊗ᴸ_R A`, the
  map `τ` intertwines `s` and its reduction `S ⊗ᴸ_{S'} s` (`Mod.derivedExtendScalarsReduction`).

The computation of `t` on K-flat complexes, and its compatibility with the connecting morphisms
of the reduction triangles, are in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransitionComplex`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S' S : C} [MonObj R] [MonObj S'] [MonObj S] [IsCommMonObj R] [IsCommMonObj S']
  [IsCommMonObj S] (φ' : R ⟶ S') [IsMonHom φ'] (ψ : S' ⟶ S) [IsMonHom ψ] (φ : R ⟶ S)
  [IsMonHom φ] (h : φ' ≫ ψ = φ)

/-! ### The derived transition -/

/-- The derived transition `τ : S' ⊗ᴸ_R K ⟶ S ⊗ᴸ_R K`, as a map in `D(Mod_{S'}(C))`: the unit of
`L(Ext_ψ) ⊣ D(Res_ψ)` at `S' ⊗ᴸ_R K`, followed by the inverse of the transitivity isomorphism
`S ⊗ᴸ_R K ≅ S ⊗ᴸ_{S'} (S' ⊗ᴸ_R K)` (`Mod.derivedExtendScalarsCompIso`). -/
noncomputable def derivedExtendScalarsTransition :
    (extendScalars φ').leftDerivedFunctor ⟶
      (extendScalars φ).leftDerivedFunctor ⋙ (comap ψ).mapDerivedCategory :=
  Functor.whiskerLeft (extendScalars φ').leftDerivedFunctor
      (derivedExtendMapDerivedCategoryAdjunction ψ).unit ≫
    Functor.whiskerRight (derivedExtendScalarsCompIso φ' ψ φ h).inv (comap ψ).mapDerivedCategory

/-- **The transition between the reductions**: the natural transformation
`t : S' ⊗ᴸ_R K ⟶ S ⊗ᴸ_R K` of complexes of `R`-modules, `D(Res_φ')` of the derived transition
`Mod.derivedExtendScalarsTransition`, followed by `D(Res_φ') ∘ D(Res_ψ) ≅ D(Res_φ)`. -/
noncomputable def derivedReductionTransition :
    (extendScalars φ').leftDerivedFunctor ⋙ (comap φ').mapDerivedCategory ⟶
      (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory :=
  Functor.whiskerRight (derivedExtendScalarsTransition φ' ψ φ h) (comap φ').mapDerivedCategory ≫
    Functor.whiskerLeft (extendScalars φ).leftDerivedFunctor
      (mapDerivedCategoryComapCompIso φ' ψ φ h).hom

/-- **The transition is compatible with the units**: `K ⟶ S' ⊗ᴸ_R K ⟶ S ⊗ᴸ_R K` is the unit
`K ⟶ S ⊗ᴸ_R K`. -/
@[reassoc]
lemma unit_app_comp_derivedReductionTransition_app (K : DerivedCategory (Mod C R)) :
    (derivedExtendMapDerivedCategoryAdjunction φ').unit.app K ≫
        (derivedReductionTransition φ' ψ φ h).app K =
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K := by
  have h₁ := unit_conjugateEquiv_symm ((derivedExtendMapDerivedCategoryAdjunction φ').comp
    (derivedExtendMapDerivedCategoryAdjunction ψ)) (derivedExtendMapDerivedCategoryAdjunction φ)
    (mapDerivedCategoryComapCompIso φ' ψ φ h).hom K
  rw [Adjunction.comp_unit_app, Category.assoc] at h₁
  have h₂ := (mapDerivedCategoryComapCompIso φ' ψ φ h).hom.naturality
    ((derivedExtendScalarsCompIso φ' ψ φ h).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₂
  simp only [derivedReductionTransition, derivedExtendScalarsTransition, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  erw [h₂, reassoc_of% h₁]
  rw [← Functor.map_comp, show ((conjugateEquiv _ _).symm _).app K ≫ _ = 𝟙 _ from
    (derivedExtendScalarsCompIso φ' ψ φ h).hom_inv_id_app K, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The **reduction** `S ⊗ᴸ_{S'} s` of a morphism `s : S' ⊗ᴸ_R B ⟶ S' ⊗ᴸ_R A`, read as a morphism
`S ⊗ᴸ_R B ⟶ S ⊗ᴸ_R A` through the transitivity isomorphisms `Mod.derivedExtendScalarsCompIso`. -/
noncomputable def derivedExtendScalarsReduction {A B : DerivedCategory (Mod C R)}
    (s : (extendScalars φ').leftDerivedFunctor.obj B ⟶
      (extendScalars φ').leftDerivedFunctor.obj A) :
    (extendScalars φ).leftDerivedFunctor.obj B ⟶ (extendScalars φ).leftDerivedFunctor.obj A :=
  (derivedExtendScalarsCompIso φ' ψ φ h).hom.app B ≫
    (extendScalars ψ).leftDerivedFunctor.map s ≫ (derivedExtendScalarsCompIso φ' ψ φ h).inv.app A

/-- The derived transition intertwines a morphism `s` and its reduction. -/
@[reassoc]
lemma comp_derivedExtendScalarsTransition_app {A B : DerivedCategory (Mod C R)}
    (s : (extendScalars φ').leftDerivedFunctor.obj B ⟶
      (extendScalars φ').leftDerivedFunctor.obj A) :
    s ≫ (derivedExtendScalarsTransition φ' ψ φ h).app A =
      (derivedExtendScalarsTransition φ' ψ φ h).app B ≫
        (comap ψ).mapDerivedCategory.map (derivedExtendScalarsReduction φ' ψ φ h s) := by
  simp only [derivedExtendScalarsTransition, derivedExtendScalarsReduction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc (comap ψ).mapDerivedCategory
    ((derivedExtendScalarsCompIso φ' ψ φ h).inv.app B), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((derivedExtendMapDerivedCategoryAdjunction ψ).unit.naturality_assoc s _)

/-- The transition intertwines `D(Res_φ')` of a morphism `s : S' ⊗ᴸ_R B ⟶ S' ⊗ᴸ_R A` and
`D(Res_φ)` of its reduction. -/
@[reassoc]
lemma map_comp_derivedReductionTransition_app {A B : DerivedCategory (Mod C R)}
    (s : (extendScalars φ').leftDerivedFunctor.obj B ⟶
      (extendScalars φ').leftDerivedFunctor.obj A) :
    (comap φ').mapDerivedCategory.map s ≫ (derivedReductionTransition φ' ψ φ h).app A =
      (derivedReductionTransition φ' ψ φ h).app B ≫
        (comap φ).mapDerivedCategory.map (derivedExtendScalarsReduction φ' ψ φ h s) := by
  simp only [derivedReductionTransition, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← Functor.map_comp_assoc, comp_derivedExtendScalarsTransition_app, Functor.map_comp,
    Category.assoc]
  congr 1
  exact (mapDerivedCategoryComapCompIso φ' ψ φ h).hom.naturality _

/-- The reduction of the derived extension of scalars `S' ⊗ᴸ_R f` of a morphism `f` is
`S ⊗ᴸ_R f`. -/
lemma derivedExtendScalarsReduction_map {A B : DerivedCategory (Mod C R)} (f : B ⟶ A) :
    derivedExtendScalarsReduction φ' ψ φ h ((extendScalars φ').leftDerivedFunctor.map f) =
      (extendScalars φ).leftDerivedFunctor.map f := by
  rw [derivedExtendScalarsReduction, ← Functor.comp_map,
    ← (derivedExtendScalarsCompIso φ' ψ φ h).hom.naturality_assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- The reduction of a composite is the composite of the reductions. -/
lemma derivedExtendScalarsReduction_comp {A B D : DerivedCategory (Mod C R)}
    (s : (extendScalars φ').leftDerivedFunctor.obj B ⟶
      (extendScalars φ').leftDerivedFunctor.obj A)
    (s' : (extendScalars φ').leftDerivedFunctor.obj A ⟶
      (extendScalars φ').leftDerivedFunctor.obj D) :
    derivedExtendScalarsReduction φ' ψ φ h (s ≫ s') =
      derivedExtendScalarsReduction φ' ψ φ h s ≫ derivedExtendScalarsReduction φ' ψ φ h s' := by
  simp only [derivedExtendScalarsReduction, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

end CategoryTheory.Mod
