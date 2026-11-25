/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
import WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.ConstantPullbackIdentityCoherence

/-!
# Functoriality of pullback on étale cohomology

Source: literature/stacks-project/cohomology.tex, Section Tag 01F7 (blueprint:
proposition-cohomology-p-1-over-henselian--1)
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The pullback on étale cohomology is natural in the sheaf and compatible with composition of
morphisms: clauses (3) and (4) of proposition-cohomology-p-1-over-henselian--1. Independence
of resolutions and the remaining clauses are not stated here. -/
theorem cohomologyPullbackFunctorial {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ {G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (φ : F ⟶ G) (x : Sheaf.H F q),
      cohomologyMap (u ≫ v) G q (Sheaf.H.map φ q x) =
        Sheaf.H.map (((u ≫ v)^*[AddCommGrpCat.{u + 1}]).map φ) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      cohomologyMap u ((v)^*[AddCommGrpCat.{u + 1}].obj F) q
          (cohomologyMap v F q x) =
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} u v).hom.app F) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} Z).hom.app F) q
        (cohomologyMap (𝟙 Z) F q x) = x) := by
  refine ⟨fun φ x ↦ cohomologyMap_map (u ≫ v) q φ x, ?_, ?_⟩
  · intro x
    rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply]
    change _ = ((CategoryTheory.Abelian.Ext.mk₀
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (u ≫ v)).inv.app
        (AddCommGrpCat.of (ULift ℤ)))).comp
      (x.mapExactFunctor ((u ≫ v)^*[AddCommGrpCat.{u + 1}])) (zero_add q)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        ((upperStarComp AddCommGrpCat.{u + 1} u v).hom.app F)) (add_zero q)
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq
      ((v)^*[AddCommGrpCat.{u + 1}]) ((u)^*[AddCommGrpCat.{u + 1}])
      ((u ≫ v)^*[AddCommGrpCat.{u + 1}])
      (upperStarComp AddCommGrpCat.{u + 1} u v)]
    simp only [Iso.app_hom, Iso.symm_hom]
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc,
      constantPullbackCompositionCoherence]
  · intro x
    rw [cohomologyMap_apply]
    change ((CategoryTheory.Abelian.Ext.mk₀ _).comp (x.mapExactFunctor _) _).comp
      (CategoryTheory.Abelian.Ext.mk₀ _) (add_zero q) = x
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison
        ((𝟙 Z)^*[AddCommGrpCat.{u + 1}]) (upperStarId AddCommGrpCat.{u + 1} Z),
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc]
    simp only [Iso.app_hom, Iso.symm_hom]
    rw [constantPullbackIdentityCoherence]
    simp

end AlgebraicGeometry.Etale
