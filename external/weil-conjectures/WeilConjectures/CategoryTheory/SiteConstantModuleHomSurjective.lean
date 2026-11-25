/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.CategoryTheory.ConstantLocalModuleHom
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import WeilConjectures.CategoryTheory.SiteConstantModuleOverHom

/-! # Local surjectivity of the constant module Hom comparison

Source: Stacks Project, Modules on Sites, Tag 093T, proof of (1).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- A local map out of a finitely presented constant module comes locally from a module map. -/
theorem siteConstantModuleHom_locallySurjective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ) [Module.FinitePresentation Λ M] :
    Presheaf.IsLocallySurjective J
      (SheafOfModules.constantLocalHom (siteConstantModuleFunctor J Λ) M N) where
  imageSieve_mem {U} x := by
    let F := siteConstantModuleFunctor J Λ
    let a := SheafOfModules.localHomEquiv (F.obj M) (F.obj N) (op U) x
    let φ := siteConstantModuleLocalMap J Λ M N U a
    have hS := finitePresentation_linearLiftSieve_mem (J := J)
      (siteConstantModuleUnitSections J Λ N) φ
    apply J.superset_covering _ hS
    intro V f hf
    obtain ⟨g, hg⟩ := hf
    refine ⟨ModuleCat.ofHom g, ?_⟩
    apply (SheafOfModules.localHomEquiv _ _ (op V)).injective
    apply siteConstantModule_over_hom_ext J Λ M N V
    intro m
    rw [SheafOfModules.constantLocalHom_equiv, SheafOfModules.localHomEquiv_map_app]
    change ((F.map (ModuleCat.ofHom g)).val.app (op V))
        ((siteConstantModuleUnit J Λ M).app (op V) m) =
      a.val.app (op (Over.mk f)) ((siteConstantModuleUnit J Λ M).app (op V) m)
    rw [siteConstantModuleUnit_naturality]
    have ha := PresheafOfModules.naturality_apply a.val
      (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)).op
      ((siteConstantModuleUnit J Λ M).app (op U) m)
    have hn := NatTrans.naturality_apply (siteConstantModuleUnit J Λ M) f.op m
    change (siteConstantModuleUnit J Λ M).app (op V) m =
      (F.obj M).val.map f.op ((siteConstantModuleUnit J Λ M).app (op U) m) at hn
    change a.val.app (op (Over.mk f))
        ((F.obj M).val.map f.op ((siteConstantModuleUnit J Λ M).app (op U) m)) =
      (F.obj N).val.map f.op
        (a.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) m)) at ha
    rw [← hn] at ha
    have hgm := hg m
    change (siteConstantModuleUnit J Λ N).app (op V) (g m) =
      (F.obj N).val.map f.op
        (a.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) m)) at hgm
    exact hgm.trans ha.symm

end CategoryTheory
