/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison

/-! # Commuting squares for a lift between module injective resolutions

Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ, functoriality of alpha and beta.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

local instance localInst_ModuleCechLiftSquares_1 (R : Type u) [Ring R] (J : Type v) [Small.{u} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

/-- Applying the Cech functor and totalization to a lift of a module morphism gives
commuting squares with both comparison augmentations.
Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ, proof and final functoriality
assertion (blueprint: lem-sc-module-cech-lift-squares).

Proof: In total degree n, alpha lands in the (n,0) summand. The total map on this
summand is the Cech map of the nth component of the lift. Restriction of a global
section commutes with that component by naturality of a presheaf module morphism.
The scalar restriction at the whole space is the identity, and its identification
commutes with module maps. This proves the alpha square componentwise. Beta lands
in the (0,n) summand. The total map on this summand is the degree-n Cech map of the
zeroth component of the lift. Functoriality of the Cech functor and the equation
relating that component to the two augmentations prove the beta square. Neither
argument needs a covering hypothesis, including for the empty indexing family.
-/
theorem moduleCechLiftSquares {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (φ : F ⟶ G) (I : InjectiveResolution F)
    (J : InjectiveResolution G) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = φ ≫ J.ι.f 0) :
    let T := HomologicalComplex₂.total.map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
          CategoryTheory.cechComplexFunctor U).mapHomologicalComplex
            (ComplexShape.up ℕ) |>.map ψ) (ComplexShape.up ℕ)
    moduleCechAlpha U I ≫ T =
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ ≫ moduleCechAlpha U J ∧
    moduleCechBeta U I ≫ T =
      (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          φ.val) ≫ moduleCechBeta U J := by
  dsimp only
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    dsimp only [HomologicalComplex.comp_f, moduleCechAlpha,
      moduleCechAlphaComponent]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    dsimp [moduleCechZero]
    apply Pi.hom_ext
    intro y
    simp only [CategoryTheory.cechComplexFunctor,
      FormalCoproduct.cochainComplexFunctor_map_f, Functor.rightOp_obj, homOfLE_leOfHom,
      SheafOfModules.forget_map,
      PresheafOfModules.forgetToPresheafModuleCat_map, Category.assoc, Pi.map_π]
    change _ ≫ (Pi.lift fun z : Fin 1 → ι =>
      (I.cocomplex.X n).presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (z l)))).op) ≫
        Pi.π _ y ≫ _ =
      _ ≫ _ ≫ (Pi.lift fun z : Fin 1 → ι =>
        (J.cocomplex.X n).presheafModuleCat.map
          (homOfLE (le_top (a := ∏ᶜ fun l => U (z l)))).op) ≫ Pi.π _ y
    simp only [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    ext x
    exact PresheafOfModules.naturality_apply (ψ.f n).val
      (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op x
  · apply HomologicalComplex.Hom.ext
    funext n
    dsimp only [HomologicalComplex.comp_f, moduleCechBeta,
      moduleCechBetaComponent]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    let C := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    change (C.map (I.ι.f 0)).f n ≫ (C.map (ψ.f 0)).f n ≫ _ =
      (C.map φ).f n ≫ (C.map (J.ι.f 0)).f n ≫ _
    rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, ← C.map_comp, ← C.map_comp, hψ]
    rfl

end AlgebraicGeometry.Scheme.Modules
