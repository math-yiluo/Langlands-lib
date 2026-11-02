# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Proof module (FLT `P2M/Sol/`).

Included without change to the Lean file by Worker 293 in the proof contribution of task `d86a245c-cda3-4bba-b453-e9e7acec04b5` (smoothness descent along a surjective étale map on the source), with Worker 1224 as coauthor; copied from revision 2 of the task-`83bb1057` draft.

## Source and licence

Port of `P2M/Sol/S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT file ends with the diagnostic command `#print axioms solution`, which only prints the axioms used and adds nothing to the environment; the port drops it.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `solution` proves the statement of `Algebra.IsSmoothAt.of_isSmoothAt_of_smooth` (companion
module `Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth`).

Auxiliary lemma `SrcSmoothDescent.projective_kaehlerDifferential_of_faithfullyFlat`: for a scalar tower
`R → A → B` with `Ω[A⁄R]` finitely presented over `A`, `B` faithfully flat and formally smooth over `A` and
formally smooth over `R`, `Ω[A⁄R]` is projective. The first fundamental sequence
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` is exact, its left map is injective because `H1(L_{B/A})` vanishes
(Jacobi–Zariski, `Algebra.H1Cotangent.exact_δ_mapBaseChange`), and it splits because `Ω[B⁄A]` is projective;
so `B ⊗[A] Ω[A⁄R]` is a direct summand of the projective module `Ω[B⁄R]`, hence flat, flatness descends along
`A → B` (`Module.Flat.of_flat_tensorProduct`), and a flat finitely presented module is projective.

Proof of `solution`. Put `A = S_𝔭` and `B = T_𝔓` (with `𝔭 = 𝔓.under S`). `B` is flat over `A` with local
structure map, hence faithfully flat; it is formally smooth over `R` (hypothesis) and over `A`. `A` is formally
étale over `S`, so `Ω[A⁄R] ≅ A ⊗[S] Ω[S⁄R]` is finitely presented. By `Algebra.formallySmooth_iff` it remains
to show that `Ω[A⁄R]` is projective (auxiliary lemma) and that `H1(L_{A/R}) ≅ A ⊗[S] H1(L_{S/R})` vanishes.
After base change to `B` this module becomes `B ⊗[T] (T ⊗[S] H1(L_{S/R}))`, which maps injectively (flatness
of `B` over `T` and the ported `Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth`) into
`B ⊗[T] H1(L_{T/R}) ≅ H1(L_{B/R}) = 0`; faithful flatness of `A → B` reflects the vanishing
(`Module.FaithfullyFlat.lTensor_reflects_triviality`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.SrcSmoothDescent.projective_kaehlerDifferential_of_faithfullyFlat`
- theorem `P2MW.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth` (same contribution).
Other imports: `Mathlib`.
