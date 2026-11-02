# `Langlands.AnthropicFLT.P2M.Sol.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat`. Statement. `HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat`: if `A` is a graded `S`-algebra
whose graded pieces `𝒜 n` are flat `S`-modules and `f ∈ 𝒜 d`, then the degree-zero localization `A_(f)` is flat over
`S`.

Proof. `A`, a direct sum of flat modules, is flat, hence so is the localization `A_f`. The inclusion `A_(f) → A_f` has
an `S`-linear retraction sending `a / f^k` to `a_{k d} / f^k`, the degree-`k d` component (local `F`, `F_wd`, `retr`,
`retr_mk`, `retr_add`, `val_F_smul`). A retract of a flat module is flat.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.φ`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.algebraMap_mem`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.val_φ`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.decompose_mul_shift`
- def `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.expo`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.pow_expo`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.mem_of_pow_eq`
- def `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.F'`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.val_F'`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.smul_deg_eq`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.F'_indep`
- def `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.F`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.val_F`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.F_wd`
- def `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.retr`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.retr_mk`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.retr_add`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.AWAYFLATSOL.val_F_smul`
- theorem `P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
