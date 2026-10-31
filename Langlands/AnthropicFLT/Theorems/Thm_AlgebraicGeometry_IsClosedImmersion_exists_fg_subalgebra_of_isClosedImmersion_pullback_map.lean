/-
Ported from `Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of A₀)) [IsAffine V]
    [QuasiCompact m] [QuasiSeparated m] [LocallyOfFiniteType m]
    (hA : ∀ mA : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
        pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mA)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ mT : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ →
        IsClosedImmersion mT :=
  P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.solution m v hA s
