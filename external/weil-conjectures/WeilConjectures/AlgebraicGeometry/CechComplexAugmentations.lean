/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import all WeilConjectures.AlgebraicGeometry.ModuleCechComparison

/-! # Functorial augmentations of arbitrary module Cech total complexes

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: def-sc-cech-complex-augmentations)
-/

@[expose] public section

universe v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

local instance instHasLimitsOfShape_cechComplexAugmentations
    (R : Type v) [Ring R] (J : Type w) [Small.{v} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{v} R) :=
  ModuleCat.hasLimitsOfShape

/-- The functor applying Cech termwise to a module complex.
Source: Stacks 01FD (blueprint: def-sc-cech-complex-augmentations). -/
def moduleCechDoubleFunctor {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens) :
    CochainComplex X.Modules ℕ ⥤
      HomologicalComplex₂ (ModuleCat.{v} Γ(X, ⊤)) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
      cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)

/-- Apply the module Cech functor termwise and totalize.
Source: Stacks 01FD (blueprint: def-sc-cech-complex-augmentations). -/
def moduleCechTotalFunctor {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens) :
    CochainComplex X.Modules ℕ ⥤ CochainComplex (ModuleCat.{v} Γ(X, ⊤)) ℕ :=
  moduleCechDoubleFunctor U ⋙
    HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℕ)

/-- Components of the map from global sections of the resolution to its Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
noncomputable def moduleCechComplexAlphaComponent {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).X n ⟶
      (((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ)).X n :=
  moduleCechZero U (K.X n) ≫
    ((moduleCechDoubleFunctor U).obj K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)

/-- The alpha components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-cech-complex-augmentations).
Proof: restrictions commute with the resolution differential. The Čech differential
of the restrictions of a global section is zero. The total differential on the (n,0)
summand is the resolution differential plus (-1)^n times that zero differential. -/
theorem moduleCechComplexAlpha_comm {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    (K : CochainComplex X.Modules ℕ) (n m : ℕ) :
    moduleCechComplexAlphaComponent U K n ≫
        (((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ)).d n m =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).d n m ≫ moduleCechComplexAlphaComponent U K m := by
  by_cases hnm : n + 1 = m
  · dsimp only [moduleCechComplexAlphaComponent]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      Category.assoc, Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ hnm 0 m (by simp [← hnm]),
      HomologicalComplex₂.d₂_eq' _ _ n (show (0 : ℕ) + 1 = 1 from rfl)]
    dsimp
    simp only [one_smul, Linear.comp_units_smul]
    have hv : moduleCechZero U (K.X n) ≫
        (((moduleCechDoubleFunctor U).obj K).X n).d 0 1 = 0 := by
      change moduleCechZero U (K.X n) ≫
        ((CategoryTheory.cechComplexFunctor U).obj
          (K.X n).presheafModuleCat).d 0 1 = 0
      exact moduleCechZero_d U (K.X n)
    simp only [← Category.assoc, hv,
      zero_comp, smul_zero, add_zero]
    have hh : moduleCechZero U (K.X n) ≫
        (((moduleCechDoubleFunctor U).obj K).d n m).f 0 =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).d n m ≫
        moduleCechZero U (K.X m) := by
      change moduleCechZero U (K.X n) ≫
        ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (K.d n m).val)).f 0 =
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (K.d n m) ≫
          moduleCechZero U (K.X m)
      exact moduleCechZero_naturality U (K.d n m)
    rw [hh]
    rfl
  · rw [HomologicalComplex.shape _ _ _ hnm, HomologicalComplex.shape _ _ _ hnm]
    simp

/-- The map alpha of Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
noncomputable def moduleCechComplexAlpha {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    (K : CochainComplex X.Modules ℕ) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K ⟶
      ((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ) where
  f := moduleCechComplexAlphaComponent U K
  comm' := fun n m _ => moduleCechComplexAlpha_comm U K n m

/-- Components of the augmentation beta into the Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
noncomputable def moduleCechComplexBetaComponent {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (K : CochainComplex X.Modules ℕ)
    (a : F ⟶ K.X 0) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).X n ⟶
      (((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ)).X n :=
  ((CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (a).val)).f n ≫
    ((moduleCechDoubleFunctor U).obj K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

/-- The beta components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-cech-complex-augmentations).
Proof: Čech differentials commute with the augmentation. The augmentation followed by
the resolution differential is zero. On the (0,n) summand the Čech differential has sign +1. -/
theorem moduleCechComplexBeta_comm {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    {F : X.Modules} (K : CochainComplex X.Modules ℕ)
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) (n m : ℕ) :
    moduleCechComplexBetaComponent U K a n ≫
        (((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ)).d n m =
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d n m ≫
        moduleCechComplexBetaComponent U K a m := by
  by_cases h : n + 1 = m
  · subst m
    dsimp [moduleCechComplexBetaComponent]
    rw [HomologicalComplex₂.total_d, Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [HomologicalComplex₂.d₁_eq' _ _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
      HomologicalComplex₂.d₂_eq _ _ 0 (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
        (n + 1) (by simp)]
    simp only [PresheafOfModules.forgetToPresheafModuleCat_map, ComplexShape.ε₁_def,
      one_smul, ComplexShape.ε₂_def, ComplexShape.ε_zero, Preadditive.comp_add]
    let T := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    have hz : a ≫ K.d 0 1 = 0 := by
      exact ha
    have hz' : (T.map (a)).f n ≫ (T.map (K.d 0 1)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, ← T.map_comp, hz, T.map_zero]
      rfl
    have hc := (T.map (a)).comm n (n + 1)
    change (T.map (a)).f n ≫ (T.map (K.d 0 1)).f n ≫ _ +
      (T.map (a)).f n ≫ (T.obj (K.X 0)).d n (n + 1) ≫ _ = _
    rw [← Category.assoc, hz', zero_comp, zero_add, ← Category.assoc, hc,
      Category.assoc]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h]
    simp

/-- The map beta of Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
noncomputable def moduleCechComplexBeta {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    {F : X.Modules} (K : CochainComplex X.Modules ℕ)
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat ⟶
      ((moduleCechDoubleFunctor U).obj K).total (ComplexShape.up ℕ) where
  f := moduleCechComplexBetaComponent U K a
  comm' := fun n m _ => moduleCechComplexBeta_comm U K a ha n m


/-- Restriction of global sections commutes with every map of coefficient complexes.
Source: Stacks 01FD, the lower squares (blueprint: def-sc-cech-complex-augmentations). -/
theorem moduleCechComplexAlpha_naturality {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {K L : CochainComplex X.Modules ℕ} (ψ : K ⟶ L) :
    moduleCechComplexAlpha U K ≫ (moduleCechTotalFunctor U).map ψ =
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ ≫ moduleCechComplexAlpha U L := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (moduleCechZero U (K.X n) ≫ _) ≫
      (HomologicalComplex₂.total.map ((moduleCechDoubleFunctor U).map ψ) _).f n =
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (ψ.f n) ≫
      moduleCechZero U (L.X n) ≫ _
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  simpa only [Category.assoc, moduleCechDoubleFunctor,
    Functor.mapHomologicalComplex_map_f, Functor.comp_map, SheafOfModules.forget_map] using
    congrArg (fun k ↦ k ≫ ((moduleCechDoubleFunctor U).obj L).ιTotal
      (ComplexShape.up ℕ) n 0 n (by simp)) (moduleCechZero_naturality U (ψ.f n))

/-- An augmentation-preserving map commutes with the coefficient augmentation into totals.
Source: Stacks 01FD, the pentagon (blueprint: def-sc-cech-complex-augmentations). -/
theorem moduleCechComplexBeta_naturality {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} {K L : CochainComplex X.Modules ℕ}
    (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : F ⟶ L.X 0) (hb : b ≫ L.d 0 1 = 0) (ψ : K ⟶ L)
    (hψ : a ≫ ψ.f 0 = b) :
    moduleCechComplexBeta U K a ha ≫ (moduleCechTotalFunctor U).map ψ =
      moduleCechComplexBeta U L b hb := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        a.val)).f n ≫ _) ≫
      (HomologicalComplex₂.total.map ((moduleCechDoubleFunctor U).map ψ) _).f n = _
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  let T := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
      cechComplexFunctor U
  change (T.map a).f n ≫ (T.map (ψ.f 0)).f n ≫ _ = (T.map b).f n ≫ _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← T.map_comp, hψ]


/-- The general alpha specializes to the existing resolution alpha.
Source: Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
theorem moduleCechComplexAlpha_resolution {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F) :
    moduleCechComplexAlpha U I.cocomplex = moduleCechAlpha U I := rfl

/-- The general beta specializes to the existing resolution beta.
Source: Stacks 01EQ (blueprint: def-sc-cech-complex-augmentations). -/
theorem moduleCechComplexBeta_resolution {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F)
    (h : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0) :
    moduleCechComplexBeta U I.cocomplex (I.ι.f 0) h = moduleCechBeta U I := rfl


end
end AlgebraicGeometry.Scheme.Modules
