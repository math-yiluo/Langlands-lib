/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Proper pushforward of extension by zero
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- The fully faithful inclusion detects zero objects via cohomology.
private theorem isZero_plus_of_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory.Plus C)
    (hK : ∀ n : ℤ, Limits.IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj K)) :
    Limits.IsZero K := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply DerivedCategory.Plus.ι.map_injective
  have hz : Limits.IsZero (DerivedCategory.Plus.ι.obj K) :=
    (DerivedCategory.isZero_iff _).2 hK
  exact hz.eq_of_src _ _

-- Lift the existing disjoint-range vanishing to D⁺ using exactness.
private theorem isZero_restrict_extensionZero (Λ : Type (u + 1)) [CommRing Λ]
    {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
    (hji : Disjoint (Set.range j.base) (Set.range i.base))
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Limits.IsZero ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)) := by
  apply isZero_plus_of_homology
  intro n
  exact (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    (ModuleCat.{u + 1} Λ) j i hji
      ((DerivedCategory.Plus.homologyFunctor _ n).obj K)).of_iso
    ((upperStar (ModuleCat.{u + 1} Λ) i).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) n).symm.app K)) |>.of_iso
    ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (upperStar (ModuleCat.{u + 1} Λ) i) n).symm.app _)

-- The derived unit is invertible, so the right triangle makes the restricted counit
-- invertible. No computation of the construction of the specified identification is needed.
private theorem isIso_restrict_comparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
      (properOpenComparison Λ f j₁ j₂ h K)) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} Λ) j₂
  have ha := a.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryPlusCompIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂)
      (upperStar (ModuleCat.{u + 1} Λ) j₂)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (asIso (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j₂).unit).symm ≪≫
      Functor.mapDerivedCategoryPlusIdIso _)
  have := ha.full
  have := ha.faithful
  have : IsIso a.unit := inferInstance
  have hc : IsIso ((upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
      (a.counit.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)))) := by
    rw [← IsIso.inv_eq_of_hom_inv_id (a.right_triangle_components
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)))]
    infer_instance
  dsimp only [properOpenComparison]
  rw [Functor.map_comp]
  exact inferInstance

/-- The specified proper/open comparison is an isomorphism for every comparison datum. -/
theorem isIso_properOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (properOpenComparison Λ f j₁ j₂ h K) := by
  classical
  apply (DerivedCategory.Plus.isIso_iff _).2
  intro n
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
  let s := T₂.algClosurePoint x
  by_cases hs : s.base (IsLocalRing.closedPoint _) ∈ Set.range j₂.base
  · have hr := isIso_restrict_comparison Λ f j₁ j₂ h K
    have hh : IsIso ((upperStar (ModuleCat.{u + 1} Λ) j₂).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          (properOpenComparison Λ f j₁ j₂ h K))) :=
      (NatIso.isIso_map_iff
        ((upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlusHomologyFunctorIso n)
        (properOpenComparison Λ f j₁ j₂ h K)).2 (by
          rw [Functor.comp_map]
          infer_instance)
    have hp := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
      (ModuleCat.{u + 1} Λ) j₂ _ hh
      (IsOpenImmersion.lift j₂ s (Scheme.range_base_subset_of_closedPoint_mem s hs))
    rw [IsOpenImmersion.lift_fac] at hp
    exact hp
  · have hdisj : Disjoint (Set.range j₂.base) (Set.range s.base) := by
      rw [Set.disjoint_right]
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint _)]
    have h₁ := isZero_restrict_extensionZero Λ j₂ s hdisj K
    have hdisj' : Disjoint (Set.range j₁.base)
        (Set.range (Limits.pullback.fst f s).base) := by
      rw [Set.disjoint_iff]
      rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      refine hdisj.ne_of_mem ⟨a, rfl⟩ ⟨(Limits.pullback.snd f s).base b, rfl⟩ ?_
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply, ← hb,
        ← Scheme.Hom.comp_apply, Limits.pullback.condition]
    have hF := isZero_restrict_extensionZero Λ j₁ (Limits.pullback.fst f s) hdisj' K
    have hb := isIso_geometricFiber_finite Λ f _ s
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)
    let : (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
        (Limits.pullback.snd f s)).Additive :=
      (derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) (Limits.pullback.snd f s)).right_adjoint_additive
    have h₂ := (Functor.map_isZero
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (Limits.pullback.snd f s)) hF).of_iso
      (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f s).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)))
    have hr : IsIso ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.map
        (properOpenComparison Λ f j₁ j₂ h K)) :=
      ⟨⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
    have hh : IsIso ((upperStar (ModuleCat.{u + 1} Λ) s).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          (properOpenComparison Λ f j₁ j₂ h K))) :=
      (NatIso.isIso_map_iff
        ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlusHomologyFunctorIso n)
        (properOpenComparison Λ f j₁ j₂ h K)).2 (by
          rw [Functor.comp_map]
          infer_instance)
    have hp := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
      (ModuleCat.{u + 1} Λ) s _ hh (𝟙 _)
    rw [Category.id_comp] at hp
    exact hp

end AlgebraicGeometry.Etale
