/-
Adapted from the Library module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`,
itself ported from the Anthropic Lean formalization of Fermat's Last Theorem (commit
6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the theorem `HilbP.main` of that module is repeated with the additional conclusion
`IsHProjective πC`; the proof keeps the closed immersion of the graded Hilbert scheme into
projective space, which `HilbP.main` discards. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe uz


attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module
attribute [-instance] ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec
attribute [-simp] DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
open _root_.CategoryTheory.MonoidalCategory
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily

open P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.HilbP

section Embedding

attribute [local instance] Langlands.ULiftInt.algebra

/-- The base change `HS = H ×_ℤ Spec S` of a scheme `H` with a closed immersion into projective
space over `ULift ℤ`, commuting with the structure morphisms, is H-projective over `S`. -/
theorem isHProjective_πHS {H : Scheme.{uz}} (pH : H ⟶ Spec (CommRingCat.of (ULift.{uz} ℤ)))
    (S : Type uz) [CommRing S] (N : ℕ)
    (ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{uz} ℤ)))
    [IsClosedImmersion ιP] (hιP : ιP ≫ ProjSpace.π (ULift.{uz} ℤ) N = pH) :
    IsHProjective (πHS H pH S) :=
  IsHProjective.of_isPullback (p := pH)
    ⟨N, (ιP : H ⟶ ProjectiveSpace (ULift.{uz} ℤ) N), ‹IsClosedImmersion ιP›,
      by rw [← hιP]; rfl⟩ (IsPullback.of_hasPullback _ _)

end Embedding

set_option maxHeartbeats 6400000 in
/-- The FLT per-polynomial Hilbert scheme theorem (`HilbP.main`), with the additional
conclusion that the representing scheme `C` is H-projective over `Spec S`. -/
theorem exists_isHProjective_hilbertPolynomial_piece
    (S : Type uz) [CommRing S] {X : Scheme.{uz}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (P : Polynomial ℚ) :
    ∃ (C : Scheme.{uz}) (πC : C ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s πC),
      (∀ (S' S'' : Type uz) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (Z'' : Scheme.{uz}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (hHP'' : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι'' ≫ pullback.snd f s'')
              (Nat.rec (motive := fun _ => Z''.Modules) (𝟙_ Z''.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp hHP).1) ∧
      (∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πC),
        ∃ (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
          pt S' s Z ι hι hfl hfp hHP = x) ∧
      (∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{uz}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
          (hHP : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (hHP' : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        pt S' s Z ι hι hfl hfp hHP = pt S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsProper πC ∧ LocallyOfFinitePresentation πC ∧
      IsHProjective πC := by
  classical
  obtain ⟨n, 𝔓, hci⟩ := hX₂
  haveI := hci

  obtain ⟨D4, hD4⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n
  by_cases hPn : ∃ (K : Type uz) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)
  ·
    obtain ⟨D1, hD1⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf n P hPn
    obtain ⟨D2, hD2⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf n P hPn
    obtain ⟨D3, hD3⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n P hPn
    obtain ⟨K₀, _, I₁, hI₁, d₁, hd₁⟩ := hPn
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ : ∃ m : ℕ, D1 ≤ m ∧ D2 ≤ m ∧ D3 ≤ m ∧ D4 P ≤ m ∧ d₁ ≤ m :=
      ⟨D1 + D2 + D3 + D4 P + d₁, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨H, pH, ptH, hbcH, hnatH, hoverH, hpropH, hlfpH, -, NP, ιP, hιP, hιPπ⟩ := hD1 m hm1
    obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4, hΦ5, hΦ6⟩ := hD2 m hm2
    have hK4 := hD3 m hm3

    haveI : LocallyOfFinitePresentation (𝔓.toProj ≫ ProjSpace.π S n) := by rw [𝔓.toProj_π]; infer_instance
    obtain ⟨I₀, hfg, hI₀, hker⟩ :=
      AlgebraicGeometry.ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion S n X 𝔓.toProj

    obtain ⟨C, ιC, hCci, hClfp, hC⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
        S n (hilbertFunctionOf n P m) hbcH (HS H pH S) (πHS H pH S) (ptHS H pH ptH hoverH S)
        (hnatHS H pH ptH hoverH S hnatH) I₀ hI₀ hfg m
    haveI := hCci
    haveI := hClfp
    haveI : IsProper pH := hpropH
    haveI : LocallyOfFinitePresentation pH := hlfpH

    have KEY : ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        ∃ p : Point S' n (hilbertFunctionOf n P m),
          (∃ c : Spec (CommRingCat.of S') ⟶ C, c ≫ ιC = (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom p).1) ∧
          (∃ φ : (Φ S' p).1 ≅ Z, φ.hom ≫ ι ≫ emb 𝔓 S' s (Spec.preimage s).hom (preimage_spec s) = (Φ S' p).2) := by
      intro S' _ s Z ι hι hfl hfp hHP
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hιZ : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      have hπ : (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n = ι ≫ pullback.snd f s := by
        rw [Category.assoc, emb_π]
      have hflZ : Flat ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by rw [hπ]; exact hfl
      have hfpZ : LocallyOfFinitePresentation ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by
        rw [hπ]; exact hfp

      obtain ⟨J, _, r, hr, hJ⟩ := hD4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ

      have fib : ∀ (k : Type uz) [Field k] [IsAlgClosed k] [Algebra S' k]
          (Zk : Scheme.{uz}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
          IsClosedImmersion ιk →
          IsPullback e (ιk ≫ ProjSpace.π k n) ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n)
            (Spec.map (CommRingCat.ofHom (algebraMap S' k))) →
          e ≫ (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) = ιk ≫ ProjSpace.map S' k n →
          ∃ q : Point k n (hilbertFunctionOf n P m), ∀ (d : ℕ), m ≤ d →
            ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
              (F ∈ q.I ↔ ∀ i : Fin (n + 1),
              (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })) = 0) := by
        intro k _ _ _ Zk ιk e hιk hpb hcomm
        obtain ⟨j₀, hj₀⟩ := exists_isUnit_of_span_eq_top r hr k
        obtain ⟨Pj, hPjreal, hPj⟩ := hJ j₀

        obtain ⟨q₁, Zk₁, ιk₁, e₁, hιk₁, hpb₁, hcomm₁, hZk₁⟩ := hPj (D4 Pj) le_rfl k hj₀
        have hpb₁' : IsPullback e₁ (ιk₁ ≫ ProjSpace.π k n) (ι ≫ pullback.snd f s)
            (Spec.map (CommRingCat.ofHom (algebraMap S' k))) := by rw [← hπ]; exact hpb₁
        obtain ⟨d₀, hd₀⟩ :=
          AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
            S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs Z ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
            (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k (algebraMap S' k) Pj (D4 Pj) q₁ Zk₁ ιk₁ hιk₁ e₁ hpb₁'
            hcomm₁.symm hZk₁
        obtain ⟨d₀', hd₀'⟩ := hHP k (algebraMap S' k)
        obtain ⟨Kj, _, Ij, hIj, dj, hdj⟩ := hPjreal
        have hPeq : Pj = P := by
          refine poly_eq_of_eval_eq Pj P (d₀ + d₀' + D4 Pj + dj) fun d hd => ?_
          have a := hd₀ d (by omega)
          have b := hd₀' d (by omega)
          have c := cast_hilbertFunctionOf n Pj Ij dj hdj (D4 Pj) d (by omega) (by omega)
          rw [← c, ← a]
          exact b
        subst hPeq

        obtain ⟨q, Zk₂, ιk₂, e₂, hιk₂, hpb₂, hcomm₂, hZk₂⟩ := hPj m hm4 k hj₀
        obtain ⟨φ, hφ₁, -⟩ :=
          AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map n S' k Z
            (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) Zk₂ ιk₂ e₂ hpb₂ hcomm₂ Zk ιk e hpb hcomm
        refine ⟨q, fun d hd F hF => ?_⟩
        rw [hZk₂ d hd F hF]
        refine forall_congr' fun i => ?_
        rw [← hφ₁, Scheme.Hom.comp_app]
        change φ.hom.app _ (ιk.app _ _) = 0 ↔ _
        constructor
        · intro h0
          apply (ConcreteCategory.bijective_of_isIso
            (φ.hom.app (ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))).1
          rw [h0, map_zero]
        · intro h0
          rw [h0, map_zero]
      obtain ⟨p, hp⟩ := hK4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ fib

      haveI := (hΦ1 S' p).1
      have hK5 : Scheme.Hom.ker (Φ S' p).2 = Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        AlgebraicGeometry.ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion n S' Z _ hιZ m _
          (fun i => by rw [hΦ6 S' p i, hp])
      haveI := IsClosedImmersion.isIso_lift (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm
      refine ⟨p, ?_, ⟨asIso (IsClosedImmersion.lift (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm.le), ?_⟩⟩
      ·
        refine (hC S' (Spec.preimage s).hom p).mpr ?_
        intro d hd F hFI hF
        rw [hp]
        refine Ideal.subset_span ⟨d, hF, hd, fun i => ?_⟩
        have h0 := app_emb_eq_zero 𝔓 S' s (Spec.preimage s).hom hs hci I₀ hI₀ hker d F hF hFI i
        rw [Scheme.Hom.comp_app]
        change ι.app _ ((emb 𝔓 S' s (Spec.preimage s).hom hs).app _ _) = 0
        rw [h0, map_zero]
      · exact IsClosedImmersion.lift_fac (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm.le

    let ptF : ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        SchemeHomOver s (ιC ≫ πHS H pH S) :=
      fun S' _ s Z ι hι hfl hfp hHP =>
        ⟨(KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose, by
          rw [← Category.assoc, (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose_spec]
          exact (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom _).2.trans (preimage_spec s).symm⟩
    refine ⟨C, ιC ≫ πHS H pH S, ptF, ?_, ?_, ?_, inferInstance, inferInstance, ?_⟩
    ·
      intro S' S'' _ _ ψ' s s'' hs' Z ι hι hfl hfp hHP Z'' ι'' hι'' hfl'' hfp'' hHP'' e hpb hcomm
      have hs := preimage_spec s
      have hs'' := preimage_spec s''

      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      letI alg'' : Algebra S' S'' := ψ'.toAlgebra
      letI algS'' : Algebra S S'' := (Spec.preimage s'').hom.toAlgebra
      have hψeq : (Spec.preimage s'').hom = ψ'.comp (Spec.preimage s).hom := by
        apply HilbR_ringHom_eq_of_specMap_eq
        rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hs, hs']
        exact hs''.symm
      haveI : IsScalarTower S S' S'' := IsScalarTower.of_algebraMap_eq (fun x => by
        change (Spec.preimage s'').hom x = ψ' ((Spec.preimage s).hom x)
        rw [hψeq]; rfl)
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hj'' : IsClosedImmersion (emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') :=
        isClosedImmersion_emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'' hci

      have hembc : pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ')) (𝟙 _)
            (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs']) ≫
          emb 𝔓 S' s (Spec.preimage s).hom hs =
          emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'' ≫ ProjSpace.map S' S'' n := by
        apply (ProjSpace.isPullback_map S S' n).hom_ext
        · rw [Category.assoc, emb_map, Category.assoc, map_comp_map S S' S'' n, emb_map]
          delta pullback.map
          rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.id_comp]
        · rw [Category.assoc, emb_π, Category.assoc, (ProjSpace.isPullback_map S' S'' n).w, ← Category.assoc, emb_π]
          delta pullback.map
          rw [pullback.lift_snd]

      have hsp := (KEY S' s Z ι hι hfl hfp hHP).choose_spec
      have hsp'' := (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose_spec
      obtain ⟨φ, hφ⟩ := hsp.2
      obtain ⟨φ'', hφ''⟩ := hsp''.2
      haveI := (hΦ1 S' (KEY S' s Z ι hι hfl hfp hHP).choose).1
      obtain ⟨q, hq⟩ := hbcH S' S'' ψ' (KEY S' s Z ι hι hfl hfp hHP).choose
      obtain ⟨eq, hpbq, hcommq⟩ := hΦ3 S' S'' (KEY S' s Z ι hι hfl hfp hHP).choose q hq

      have t : IsPullback φ.hom ((Φ S' (KEY S' s Z ι hι hfl hfp hHP).choose).2 ≫ ProjSpace.π S' n)
          ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) (𝟙 _) :=
        IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, hφ]⟩
      have h₁ := hpbq.paste_horiz t
      rw [Category.comp_id] at h₁
      have h₂ : IsPullback e ((ι'' ≫ emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') ≫ ProjSpace.π S'' n)
          ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n)
          (Spec.map (CommRingCat.ofHom (algebraMap S' S''))) := by
        rw [Category.assoc, emb_π, Category.assoc, emb_π]
        exact hpb
      obtain ⟨E, hE₁, -⟩ :=
        AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map n S' S'' Z
          (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
          (Φ S'' q).1 (Φ S'' q).2 (eq ≫ φ.hom) h₁ (by rw [Category.assoc, hφ, hcommq])
          Z'' (ι'' ≫ emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') e h₂
          (by rw [← Category.assoc, ← hcomm, Category.assoc, hembc, Category.assoc])
      have hpq : (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose = q := by
        refine hΦ2 S'' _ q ⟨φ'' ≪≫ E.symm, ?_⟩
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, E.inv_comp_eq.mpr hE₁.symm, hφ'']

      change (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose_spec.1.choose =
        Spec.map (CommRingCat.ofHom ψ') ≫ (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose
      rw [← cancel_mono ιC, hsp''.1.choose_spec, Category.assoc, hsp.1.choose_spec, hpq,
        ← hnatHS H pH ptH hoverH S hnatH S' S'' (Spec.preimage s).hom ψ' _ q hq]
      apply pullback.hom_ext
      · rw [ptHS_fst, ptHS_fst]
      · rw [(ptHS H pH ptH hoverH S S'' (Spec.preimage s'').hom q).2,
          (ptHS H pH ptH hoverH S S'' (ψ'.comp (Spec.preimage s).hom) q).2, hψeq]
    ·
      intro S' _ s x
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra

      let v : SchemeHomOver (Spec.map (CommRingCat.ofHom (Spec.preimage s).hom)) (πHS H pH S) :=
        ⟨x.1 ≫ ιC, by rw [Category.assoc]; exact x.2.trans hs⟩
      let p : Point S' n (hilbertFunctionOf n P m) := (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom).symm v
      have hpv : (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom p).1 = x.1 ≫ ιC := by
        change (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom ((ptHS H pH ptH hoverH S S' _).symm v)).1 = _
        rw [Equiv.apply_symm_apply]
      have hcond := (hC S' (Spec.preimage s).hom p).mp ⟨x.1, hpv.symm⟩
      haveI := (hΦ1 S' p).1
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci

      have hle : Scheme.Hom.ker (emb 𝔓 S' s (Spec.preimage s).hom hs) ≤ Scheme.Hom.ker (Φ S' p).2 := by
        refine Scheme.IdealSheafData.le_of_iSup_eq_top
          (fun i : Fin (n + 1) => (⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i)
              (ProjSpace.X_mem_one S' n i) one_pos⟩ : (PPn S' n).affineOpens))
          (Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S' n)) fun i => ?_
        rw [ker_emb_ideal 𝔓 S' s (Spec.preimage s).hom hs hci I₀ hI₀ hker i, hΦ6 S' p i]
        apply Ideal.span_mono
        rintro _ ⟨d, F, hF, hFI, rfl⟩
        by_cases hmd : m ≤ d
        · exact ⟨d, F, hF, hcond d hmd F hFI hF, rfl⟩
        ·
          have hdm : d ≤ m := le_of_lt (not_le.mp hmd)
          have hG : (MvPolynomial.X i ^ (m - d) * F).IsHomogeneous m := by
            have := (MvPolynomial.isHomogeneous_X_pow i (m - d)).mul hF
            rwa [Nat.sub_add_cancel hdm] at this
          refine ⟨m, MvPolynomial.X i ^ (m - d) * F, hG, hcond m le_rfl _ (Ideal.mul_mem_left _ _ hFI) hG, ?_⟩
          congr 1
          apply HomogeneousLocalization.val_injective
          simp only [HomogeneousLocalization.val_mk]
          rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          refine ⟨1, ?_⟩
          simp only [OneMemClass.coe_one, one_mul]
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hdm]
      let ι : (Φ S' p).1 ⟶ pullback f s := IsClosedImmersion.lift (emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hle
      have hιfac : ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs = (Φ S' p).2 := IsClosedImmersion.lift_fac _ _ _
      have hιci : IsClosedImmersion ι := by
        haveI : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by rw [hιfac]; infer_instance
        exact IsClosedImmersion.of_comp ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
      have hsnd : ι ≫ pullback.snd f s = (Φ S' p).2 ≫ ProjSpace.π S' n := by
        rw [← emb_π 𝔓 S' s (Spec.preimage s).hom hs, ← Category.assoc, hιfac]
      have hιfl : Flat (ι ≫ pullback.snd f s) := by rw [hsnd]; exact (hΦ1 S' p).2.1
      have hιfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s) := by rw [hsnd]; exact (hΦ1 S' p).2.2
      have hιHP : (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => (Φ S' p).1.Modules) (𝟙_ (Φ S' p).1.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) := by
        intro k _ _ sk
        letI : Algebra S' k := sk.toAlgebra
        obtain ⟨q, hq⟩ := hbcH S' k sk p
        obtain ⟨eq, hpbq, hcommq⟩ := hΦ3 S' k p q hq
        obtain ⟨d₀, hd₀⟩ :=
          AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
            S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs (Φ S' p).1 ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
            (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k sk P m q (Φ k q).1 (Φ k q).2 (hΦ1 k q).1 eq
            (by rw [hsnd]; exact hpbq) (by rw [hιfac]; exact hcommq.symm) (hΦ5 k q)
        refine ⟨d₀ + m + d₁, fun d hd => ?_⟩
        rw [hd₀ d (by omega)]
        exact cast_hilbertFunctionOf n P I₁ d₁ hd₁ m d (by omega) (by omega)
      refine ⟨(Φ S' p).1, ι, hιci, hιfl, hιfp, hιHP, ?_⟩

      have hspec := (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose_spec
      obtain ⟨φZ, hφZ⟩ := hspec.2
      have hpZ : (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose = p := by
        refine hΦ2 S' _ p ⟨φZ, ?_⟩
        rw [← hιfac]
        exact hφZ
      apply Subtype.ext
      change (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose_spec.1.choose = x.1
      rw [← cancel_mono ιC, hspec.1.choose_spec, hpZ, hpv]
    ·
      intro S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' hHP hHP' heq
      have hs := preimage_spec s
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      have hsp := (KEY S' s Z ι hι hfl hfp hHP).choose_spec
      have hsp' := (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose_spec
      obtain ⟨φ, hφ⟩ := hsp.2
      obtain ⟨φ', hφ'⟩ := hsp'.2
      have hcc : (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose =
          (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose_spec.1.choose := congrArg Subtype.val heq
      have hpt : (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom (KEY S' s Z ι hι hfl hfp hHP).choose).1 =
          (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose).1 := by
        rw [← hsp.1.choose_spec, ← hsp'.1.choose_spec, hcc]
      have hpp : (KEY S' s Z ι hι hfl hfp hHP).choose = (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose :=
        (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom).injective (Subtype.ext hpt)
      have hk : Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) =
          Scheme.Hom.ker (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
        have e1 : Scheme.Hom.ker (Φ S' (KEY S' s Z ι hι hfl hfp hHP).choose).2 =
            Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
          rw [← hφ, Scheme.Hom.ker_comp_of_isIso]
        have e2 : Scheme.Hom.ker (Φ S' (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose).2 =
            Scheme.Hom.ker (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
          rw [← hφ', Scheme.Hom.ker_comp_of_isIso]
        rw [← e1, ← e2, hpp]
      haveI : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      haveI : IsClosedImmersion (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      haveI := IsClosedImmersion.isIso_lift (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm
      refine ⟨asIso (IsClosedImmersion.lift (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm.le), ?_⟩
      have hfac := IsClosedImmersion.lift_fac (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm.le
      rw [← Category.assoc] at hfac
      exact (cancel_mono (emb 𝔓 S' s (Spec.preimage s).hom hs)).mp hfac
    · haveI := hιP
      obtain ⟨N', i', hi', hi'π⟩ := isHProjective_πHS pH S NP ιP hιPπ
      haveI := hi'
      exact ⟨N', ιC ≫ i', inferInstance, by rw [Category.assoc, hi'π]⟩
  ·
    have hno : ∀ (S' : Type uz) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{uz}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type uz) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        IsEmpty ↥(Spec (CommRingCat.of S')) := by
      intro S' _ s Z ι hι hfl hfp hHP
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨x⟩ := hne
      apply hPn

      let k : Type uz := AlgebraicClosure (FractionRing (S' ⧸ x.asIdeal))
      letI : Algebra S' k :=
        ((algebraMap (FractionRing (S' ⧸ x.asIdeal)) k).comp
          ((algebraMap (S' ⧸ x.asIdeal) (FractionRing (S' ⧸ x.asIdeal))).comp (Ideal.Quotient.mk x.asIdeal))).toAlgebra
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hιZ : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      have hπ : (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n = ι ≫ pullback.snd f s := by
        rw [Category.assoc, emb_π]
      have hflZ : Flat ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by rw [hπ]; exact hfl
      have hfpZ : LocallyOfFinitePresentation ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by
        rw [hπ]; exact hfp
      obtain ⟨J, _, r, hr, hJ⟩ := hD4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ
      obtain ⟨j₀, hj₀⟩ := exists_isUnit_of_span_eq_top r hr k
      obtain ⟨Pj, hPjreal, hPj⟩ := hJ j₀
      obtain ⟨q₁, Zk₁, ιk₁, e₁, hιk₁, hpb₁, hcomm₁, hZk₁⟩ := hPj (D4 Pj) le_rfl k hj₀
      have hpb₁' : IsPullback e₁ (ιk₁ ≫ ProjSpace.π k n) (ι ≫ pullback.snd f s)
          (Spec.map (CommRingCat.ofHom (algebraMap S' k))) := by rw [← hπ]; exact hpb₁
      obtain ⟨d₀, hd₀⟩ :=
        AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
          S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs Z ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
          (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k (algebraMap S' k) Pj (D4 Pj) q₁ Zk₁ ιk₁ hιk₁ e₁ hpb₁'
          hcomm₁.symm hZk₁
      obtain ⟨d₀', hd₀'⟩ := hHP k (algebraMap S' k)
      obtain ⟨Kj, hKj, Ij, hIj, dj, hdj⟩ := hPjreal
      have hPeq : Pj = P := by
        refine poly_eq_of_eval_eq Pj P (d₀ + d₀' + D4 Pj + dj) fun d hd => ?_
        have a := hd₀ d (by omega)
        have b := hd₀' d (by omega)
        have c := cast_hilbertFunctionOf n Pj Ij dj hdj (D4 Pj) d (by omega) (by omega)
        rw [← c, ← a]
        exact b
      subst hPeq
      exact ⟨Kj, hKj, Ij, hIj, dj, hdj⟩
    refine ⟨∅, Scheme.emptyTo _, fun S' _ s Z ι hι hfl hfp hHP =>
        haveI := hno S' s Z ι hι hfl hfp hHP
        ⟨(isInitialOfIsEmpty (X := Spec (CommRingCat.of S'))).to ∅, isInitialOfIsEmpty.hom_ext _ _⟩,
      ?_, ?_, ?_, inferInstance, inferInstance, ?_⟩
    · intro S' S'' _ _ ψ' s s'' hs' Z ι hι hfl hfp hHP Z'' ι'' hι'' hfl'' hfp'' hHP'' e hpb hcomm
      haveI := hno S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP''
      exact isInitialOfIsEmpty.hom_ext _ _
    · intro S' _ s x
      haveI hE : IsEmpty ↥(Spec (CommRingCat.of S')) := x.1.base.hom.1.isEmpty
      haveI : IsEmpty ↥(pullback f s) := (pullback.snd f s).base.hom.1.isEmpty
      refine ⟨pullback f s, 𝟙 _, inferInstance, ?_, ?_, ?_, ?_⟩
      · rw [Category.id_comp]; infer_instance
      · rw [Category.id_comp]; infer_instance
      · intro k _ _ sk
        exact (hE.false (⟨RingHom.ker sk, RingHom.ker_isPrime sk⟩ : ↥(Spec (CommRingCat.of S')))).elim
      · exact Subtype.ext (isInitialOfIsEmpty.hom_ext _ _)
    · intro S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' hHP hHP' heq
      haveI := hno S' s Z ι hι hfl hfp hHP
      haveI : IsEmpty ↥Z := (ι ≫ pullback.snd f s).base.hom.1.isEmpty
      haveI : IsEmpty ↥Z' := (ι' ≫ pullback.snd f s).base.hom.1.isEmpty
      exact ⟨(isInitialOfIsEmpty (X := Z)).uniqueUpToIso (isInitialOfIsEmpty (X := Z')),
        isInitialOfIsEmpty.hom_ext _ _⟩
    · exact ⟨0, Scheme.emptyTo _, inferInstance, isInitialOfIsEmpty.hom_ext _ _⟩

end Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily

end
