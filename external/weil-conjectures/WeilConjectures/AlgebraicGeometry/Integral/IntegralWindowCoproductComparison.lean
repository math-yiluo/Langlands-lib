/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralExtHomContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Truncations and coproducts for integral compactness

Auxiliary results for integral compactness: constant-model constructibility is invariant under
isomorphism, and canonical truncations of a derived category preserve coproducts when the
homology functors do. -/

@[expose] public noncomputable section

set_option linter.privateModule false

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CoproductsFromFiniteFiltered DirectSum

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem constant_model_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hfinite (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := h
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso e).symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hfinite (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · rw [ite_eq_left h] at hM ⊢
    exact hstrat X e hM
  · rw [ite_eq_right h] at hM ⊢
    intro U hU
    exact hstrat U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : HasCoproduct K := inferInstance
    have : HasCoproduct L := inferInstance
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_comp_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

private theorem truncLE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncLE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncLE a
  let ι := t.truncLEι a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : HasCoproduct K := inferInstance
    have : HasCoproduct L := inferInstance
    have : (∐ L).IsLE a := by
      apply (DerivedCategory.isLE_iff (∐ L) a).2
      intro q hq
      exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
        (coproductIsCoproduct L)).isZero_pt
        (Functor.isZero _ fun i ↦ DerivedCategory.isZero_of_isLE (L i.as) a q hq)
    let f : ∐ L ⟶ ∐ K := Sigma.desc (fun i ↦ ι.app (K i) ≫ Sigma.ι K i)
    let c := sigmaComparison T K
    have hcf : c ≫ ι.app (∐ K) = f := by
      apply Sigma.hom_ext
      intro i
      rw [← Category.assoc, ι_comp_sigmaComparison]
      simpa only [f, Sigma.ι_comp_desc, Functor.id_map] using ι.naturality (Sigma.ι K i)
    -- The canonical truncation triangle supplies the other half of the coproduct.
    -- Prove invertibility by testing cohomology, where truncation retains a degree or zero.
    have hc : IsIso c := by
      apply (DerivedCategory.isIso_iff A c).2
      intro n
      by_cases hn : n ≤ a
      · have hι : IsIso ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hi (i : I) : IsIso
            ((DerivedCategory.homologyFunctor A n).map (ι.app (K i))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hf : IsIso ((DerivedCategory.homologyFunctor A n).map f) := by
          let H := DerivedCategory.homologyFunctor A n
          have heq : H.map f = inv (sigmaComparison H L) ≫
              Limits.Sigma.map (fun i ↦ H.map (ι.app (K i))) ≫ sigmaComparison H K := by
            apply (cancel_epi (sigmaComparison H L)).1
            apply Sigma.hom_ext
            intro i
            simp only [ι_comp_sigmaComparison_assoc, IsIso.hom_inv_id_assoc,
              Sigma.ι_map_assoc]
            rw [← H.map_comp, Sigma.ι_comp_desc, H.map_comp]
            change H.map (ι.app (K i)) ≫ H.map (Sigma.ι K i) =
              H.map (ι.app (K i)) ≫ Sigma.ι (fun i ↦ H.obj (K i)) i ≫ sigmaComparison H K
            rw [ι_comp_sigmaComparison]
          rw [heq]
          infer_instance
        have heq : (DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)) =
            (DerivedCategory.homologyFunctor A n).map f := by
          rw [← Functor.map_comp, hcf]
        have : IsIso ((DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) := by
          rw [heq]
          exact hf
        exact IsIso.of_isIso_comp_right
          ((DerivedCategory.homologyFunctor A n).map c)
          ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)))
      · have hz₁ := DerivedCategory.isZero_of_isLE (∐ L) a n (by omega)
        have hz₂ := DerivedCategory.isZero_of_isLE (T.obj (∐ K)) a n (by omega)
        exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

end AlgebraicGeometry.ProEtale
