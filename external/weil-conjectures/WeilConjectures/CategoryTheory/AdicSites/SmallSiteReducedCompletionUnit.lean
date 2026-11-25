/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import all WeilConjectures.CategoryTheory.AdicSites.CompletionFiniteReductionSupplement

/-! # Reduction inverts the completion unit

Source: Stacks 099M, 091N; the reduction step of proposition-composition-base-change-rf-shriek Step
5.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AdicSites

private theorem finiteRestriction_complete (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) [IsNoetherianRing A] (n : ℕ)
    (M : S.derived (quotientRing A I n)) :
    S.IsComplete A I ((S.finiteRestriction A I n).obj M) := by
  let R := S.ring A
  let B := S.ring (quotientRing A I n)
  let φ := ConstantCompletion.quotient S.topology A I n
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod B) :=
    HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings B).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let P := DerivedCategory.Q.objPreimage M
  let L := (ConstantCompletion.Q R).obj
    (((ConstantCompletion.res φ).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : S.IsComplete A I L := by
    apply (ConstantCompletion.complete_iff_constantElements S.topology A I L).mpr
    intro a ha U
    apply (restrictScalars_completeElement_iff S.topology R B φ M U _).mpr
    apply completeElement_nilpotent S.topology B M U _ (n + 1)
    rw [← map_pow]
    apply RingHom.mem_ker.mp
    rw [(ConstantCompletion.flat_and_quotients S.topology A I).2.2 n U |>.2]
    apply Ideal.subset_span
    refine ⟨⟨a ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
    simp only [ConstantCompletion.constantSection, map_pow]
  let e : L ≅ (S.finiteRestriction A I n).obj M :=
    (ConstantCompletion.resFactors φ).app P ≪≫
      (ConstantCompletion.dres φ).mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact complete_iso S A I e hL

end CategoryTheory.AdicSites
