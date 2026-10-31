/-
Ported from `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the `p2m_open` commands are
replaced by `open`; the `p2m_export` commands are replaced by `export`. The paired Markdown
file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance] ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (IsProper Spec Scheme IsAffineOpen IsAffineOpen.isLocalization_basicOpen OModulePresheaf OModulePresheaf.unit OModulePresheaf.cechFinite_of_isProper)
namespace OModulePresheaf
export _root_.AlgebraicGeometry.OModulePresheaf (CechFinite IsCoherent IsQuasicoherent unit cechFinite_of_isProper)
open _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isCoherent_unit : (OModulePresheaf.unit π).IsCoherent :=
  fun U => Module.Finite.self Γ(V, U.1)

theorem isQuasicoherent_unit : (OModulePresheaf.unit π).IsQuasicoherent := by
  intro U f
  haveI := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · change ↑Γ(V, V.basicOpen f) at x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) x
    refine ⟨n, y, ?_⟩
    show (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) * x
    rw [mul_comm]
    exact h.symm
  · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Γ(V, V.basicOpen f) y).mp hy
    exact ⟨n, hn⟩

end AlgebraicGeometry.OModulePresheaf

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover) : (OModulePresheaf.unit π).CechFinite K :=
  AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper _
    (AlgebraicGeometry.OModulePresheaf.isCoherent_unit π)
    (AlgebraicGeometry.OModulePresheaf.isQuasicoherent_unit π) K
