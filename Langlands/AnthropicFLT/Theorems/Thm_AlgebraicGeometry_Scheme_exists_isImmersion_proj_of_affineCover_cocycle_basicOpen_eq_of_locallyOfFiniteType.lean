/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified in Langlands-lib, 26 November 2026: FLT module names are prefixed by
`Langlands.AnthropicFLT`; `import Mathlib` is replaced by `import Langlands.MathlibBase`; the
FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof
`by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; names that the Library renamed carry the suffix `FLT`. The paired Markdown
file lists the changes.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategoryFLT AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategoryFLT AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosedFLT SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-simp] AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSectionFLT_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPowFLT_zero AlgebraicGeometry.Scheme.Modules.tensorPowFLT_succ

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
    (B : Type) [CommRing B] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution B Y πY r V hVaff hcov w hw1 hw2 hw3
