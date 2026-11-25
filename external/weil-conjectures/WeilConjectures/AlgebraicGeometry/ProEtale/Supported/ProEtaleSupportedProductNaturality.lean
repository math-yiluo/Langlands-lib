/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct

/-! # Naturality of the actual pro-etale supported exterior product
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] HomologicalComplex₂.total
set_option backward.isDefEq.respectTransparency true
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale

open Lean Lean.Meta Lean.Elab.Tactic in
private meta def supportedStructureCongr : Nat → MVarId → TacticM Unit
  | 0, _ => throwError "structural congruence exhausted"
  | fuel + 1, g => g.withContext do
      let ty ← instantiateMVars (← g.getType)
      if let some _ := ty.eq? then
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``eq_of_heq)
        for g' in gs do supportedStructureCongr fuel g'
      else if let some (_, lhs, _, rhs) := ty.heq? then
        if lhs == rhs || (← isProof lhs) then
          g.assign (← mkHEqRefl lhs)
        else
          let f := lhs.getAppFn
          if (← isDefEq f rhs.getAppFn) && lhs.getAppNumArgs == rhs.getAppNumArgs then
            let h ← mkHCongrWithArity f lhs.getAppNumArgs
            let gs ← g.apply h.proof { synthAssignedInstances := false }
            for g' in gs do supportedStructureCongr fuel g'
          else
            unless ← isDefEq lhs rhs do
              throwError "structural congruence: different heads {f} / {rhs.getAppFn}"
            g.assign (← mkHEqRefl lhs)
      else
        g.assign (← synthInstance ty)

private theorem evaluation_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (G G' : D ⥤ E) (H : C ⥤ E)
    (σ : H ≅ F ⋙ G) (ε : R ⋙ F ⟶ 𝟭 D) (τ : G' ≅ G)
    {K K' : D} (a : K ⟶ K') :
    H.map (R.map a) ≫
        (σ.hom.app (R.obj K') ≫ G.map (ε.app K') ≫ τ.inv.app K') =
      (σ.hom.app (R.obj K) ≫ G.map (ε.app K) ≫ τ.inv.app K) ≫ G'.map a := by
  exact (Functor.whiskerLeft R σ.hom ≫ Functor.whiskerRight ε G ≫ τ.inv).naturality a

private def bifunctorMap {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {U U' V V' : D} (a : U ⟶ U') (b : V ⟶ V') :
    (T.obj U).obj V ⟶ (T.obj U').obj V' :=
  (T.map a).app V ≫ (T.obj U').map b

private theorem castFamily_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G F₁ F₂ : C ⥤ D) (T : D ⥤ D ⥤ D) (hT : T = curriedTensor D)
    (e : (∀ M N : C, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N) =
      (∀ M N : C, G.obj (M ⊗ N) ⟶ (T.obj (F₁.obj M)).obj (F₂.obj N)))
    (t : ∀ M N : C, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (ht : ∀ (M M' N N' : C) (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ (F₁.map a ⊗ₘ F₂.map b))
    {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N') :
    G.map (a ⊗ₘ b) ≫ (cast e t) M' N' = (cast e t) M N ≫
      bifunctorMap T (F₁.map a) (F₂.map b) := by
  subst T
  simpa only [cast_eq, bifunctorMap, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using ht M M' N N' a b

private theorem tensorFunctor_eq_generic
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) :
    derivedTensor C T = curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
  rfl

private theorem tensorFunctor_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    derivedTensor (ModuleCat.{u + 1} A) T =
      curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) := by
  refine Eq.mp ?_ (tensorFunctor_eq_generic (ModuleCat.{u + 1} A) T)
  run_tac do
    for g in ← Lean.Elab.Tactic.getGoals do supportedStructureCongr 40 g
    Lean.Elab.Tactic.setGoals []

private theorem comparison_cast_natural
    {C D : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (θ : ∀ P Q : CochainComplex C ℤ, SupportedTensorDerivation.ComplexHom G F₁ F₂ P Q)
    (t : SupportedTensorDerivation.ComparisonHom G F₁ F₂)
    (ht : SupportedTensorDerivation.ComparisonFamilyCondition G F₁ F₂ θ t)
    (T : DerivedCategory D ⥤ DerivedCategory D ⥤ DerivedCategory D)
    (hT : T = curriedTensor (DerivedCategory D))
    (e : SupportedTensorDerivation.ComparisonHom G F₁ F₂ =
      (∀ M N : DerivedCategory C, G.mapDerivedCategory.obj (M ⊗ N) ⟶
        (T.obj (F₁.mapDerivedCategory.obj M)).obj (F₂.mapDerivedCategory.obj N)))
    {M M' N N' : DerivedCategory C} (a : M ⟶ M') (b : N ⟶ N') :
    G.mapDerivedCategory.map (a ⊗ₘ b) ≫ (cast e t) M' N' =
      (cast e t) M N ≫ bifunctorMap T
        (F₁.mapDerivedCategory.map a) (F₂.mapDerivedCategory.map b) := by
  refine castFamily_natural G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    T hT e t ?_ a b
  intro M M' N N' a b
  simpa only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
    curriedTensor_obj_map, Category.assoc] using ht.1 M M' N N' a b

private theorem comparison_natural (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    {M M' N N' : DerivedCategory (ModuleCat.{u + 1} A)} (a : M ⟶ M') (b : N ⟶ N') :
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.map
        (a ⊗ₘ b) ≫ supportedCoefficientTensorDerived A f g i j M' N' =
      supportedCoefficientTensorDerived A f g i j M N ≫
        supportedDerivedTensorMap A (pullback f g)
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.map a)
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.map b) := by
  exact comparison_cast_natural
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorComplex A f g i j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose_spec.1
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (tensorFunctor_eq A (pullback f g))
    (supportedCoefficientTensorDerivedHom_tensor A f g i j) a b

end AlgebraicGeometry.ProEtale
