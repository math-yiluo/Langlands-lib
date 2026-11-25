/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # The coefficient unit as a generator of the rational localizing category -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩

omit [IsCommMonObj Λ] in
private theorem zero_finitelyPresented : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩

private instance pointBraided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj (0 : Modules Λ S)) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem regular_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, ite_eq_left hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular Λ (𝟙 X)⟩

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (0 : Modules Λ X) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, ite_eq_left hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X (unit Λ X) := by
  let C := Modules Λ X
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj (unit Λ X)) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff (unit Λ X) 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff (unit Λ X) 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)

attribute [-instance] internalMonoidal in
/-- Preservation of pullback followed by a shifted line implies membership of that line. -/
theorem line_localizing_of_preservation
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (L : Modules Λ X)
    (h : ∀ K, CategoryTheory.localizingClosure
        (constantModelBoundedConstructible Λ S) K →
      CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)
        ((moduleObjectDerivedPullback Λ f ⋙ twist Λ X L).obj K)) :
    CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj L) ⟦(2 : ℤ)⟧) := by
  have hU : CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ S)
      (unit Λ S) := fun Q _ hQ ↦ hQ _ (coefficientUnit_boundedConstructible Λ S)
  have e₀ : (moduleObjectDerivedPullback Λ f).obj (unit Λ S) ≅ unit Λ X :=
    (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso.app _ ≪≫
      (DerivedCategory.singleFunctor (Modules Λ X) 0).mapIso
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm
  let B := (DerivedCategory.singleFunctor (Modules Λ X) 0).obj L
  have e₁ : (moduleObjectDerivedPullback Λ f).obj (unit Λ S) ⊗ B ≅ B :=
    tensorIso e₀ (Iso.refl B) ≪≫
      whiskerRightIso (DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)) B ≪≫ λ_ B
  have e : (moduleObjectDerivedPullback Λ f ⋙ twist Λ X L).obj (unit Λ S) ≅
      B ⟦(2 : ℤ)⟧ := (shiftFunctor _ (2 : ℤ)).mapIso e₁
  intro Q hQ hgen
  have := hQ.2.1
  exact Q.prop_of_iso e ((h _ hU) Q hQ hgen)

end AlgebraicGeometry.ProEtale.RationalP1
