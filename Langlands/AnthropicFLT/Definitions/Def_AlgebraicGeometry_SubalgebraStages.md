# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Definitions module.

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_SubalgebraStages.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Fixes rings `A₀ → A`, a directed family `S : ι →o Subalgebra A₀ A` and a morphism
`f : X ⟶ Spec A₀`, and defines the inverse system of base changes of `f` along
`Spec (S i) ⟶ Spec A₀`. Definitions: the morphisms `specHom`, `specHomTop`, `specTrans` and `specLeg`
between the spectra; the diagram `specDiagram` and cone `specCone` of affine schemes; the stages
`obj i = pullback f (specHom S i)`; the transition maps `trans`; the diagram `diagram S f : ιᵒᵖ ⥤ Scheme`;
the legs `leg i` from `pullback f (Spec A ⟶ Spec A₀)`; and the cone `cone S f`. It proves the
commutation lemmas (`trans_fst`, `trans_snd`, `leg_trans`, ...), that the transition squares and legs
are pullback squares (`isPullback_trans`, `isPullback_leg`), and instances: transition maps and legs are
affine, the stages inherit quasi-compactness and quasi-separatedness from `f`, and `ιᵒᵖ` is cofiltered
when `ι` is directed and nonempty. Several of these instances and simp lemmas are switched off with
`attribute [-instance]` / `attribute [-simp]` in the modules that import this one, as in FLT.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `AlgebraicGeometry.SubalgebraStages.specHom`
- abbrev `AlgebraicGeometry.SubalgebraStages.specHomTop`
- abbrev `AlgebraicGeometry.SubalgebraStages.specTrans`
- abbrev `AlgebraicGeometry.SubalgebraStages.specLeg`
- lemma `AlgebraicGeometry.SubalgebraStages.specTrans_specHom`
- lemma `AlgebraicGeometry.SubalgebraStages.specLeg_specHom`
- lemma `AlgebraicGeometry.SubalgebraStages.specLeg_specTrans`
- lemma `AlgebraicGeometry.SubalgebraStages.specTrans_comp`
- lemma `AlgebraicGeometry.SubalgebraStages.specTrans_refl`
- def `AlgebraicGeometry.SubalgebraStages.specDiagram`
- def `AlgebraicGeometry.SubalgebraStages.specCone`
- lemma `AlgebraicGeometry.SubalgebraStages.specDiagram_obj`
- lemma `AlgebraicGeometry.SubalgebraStages.specDiagram_map`
- lemma `AlgebraicGeometry.SubalgebraStages.specCone_pt`
- lemma `AlgebraicGeometry.SubalgebraStages.specCone_π_app`
- abbrev `AlgebraicGeometry.SubalgebraStages.obj`
- def `AlgebraicGeometry.SubalgebraStages.trans`
- lemma `AlgebraicGeometry.SubalgebraStages.trans_fst`
- lemma `AlgebraicGeometry.SubalgebraStages.trans_snd`
- lemma `AlgebraicGeometry.SubalgebraStages.trans_refl`
- lemma `AlgebraicGeometry.SubalgebraStages.trans_comp`
- def `AlgebraicGeometry.SubalgebraStages.diagram`
- lemma `AlgebraicGeometry.SubalgebraStages.diagram_obj`
- lemma `AlgebraicGeometry.SubalgebraStages.diagram_map`
- lemma `AlgebraicGeometry.SubalgebraStages.diagram_map_fst`
- lemma `AlgebraicGeometry.SubalgebraStages.diagram_map_snd`
- def `AlgebraicGeometry.SubalgebraStages.leg`
- lemma `AlgebraicGeometry.SubalgebraStages.leg_fst`
- lemma `AlgebraicGeometry.SubalgebraStages.leg_snd`
- lemma `AlgebraicGeometry.SubalgebraStages.leg_trans`
- def `AlgebraicGeometry.SubalgebraStages.cone`
- lemma `AlgebraicGeometry.SubalgebraStages.cone_pt`
- lemma `AlgebraicGeometry.SubalgebraStages.cone_π_app`
- lemma `AlgebraicGeometry.SubalgebraStages.cone_π_app_fst`
- lemma `AlgebraicGeometry.SubalgebraStages.cone_π_app_snd`
- lemma `AlgebraicGeometry.SubalgebraStages.specCone_π_app_specHom`
- lemma `AlgebraicGeometry.SubalgebraStages.specDiagram_map_specHom`
- lemma `AlgebraicGeometry.SubalgebraStages.isPullback_trans`
- lemma `AlgebraicGeometry.SubalgebraStages.isPullback_leg`
- instance `AlgebraicGeometry.SubalgebraStages.isAffineHom_trans`
- instance `AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map`
- instance `AlgebraicGeometry.SubalgebraStages.isAffineHom_leg`
- instance `AlgebraicGeometry.SubalgebraStages.quasiCompact_snd`
- instance `AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd`
- instance `AlgebraicGeometry.SubalgebraStages.compactSpace_pullback`
- instance `AlgebraicGeometry.SubalgebraStages.compactSpace_obj`
- instance `AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback`
- instance `AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj`
- instance `AlgebraicGeometry.SubalgebraStages.isCofiltered_op`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
