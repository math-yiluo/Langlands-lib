# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules`. Statement. `AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules`: for a module `M` on `V` over
`π : V ⟶ Spec R` and any ordered affine cover `K`, the global sections `Γ(M, ⊤)` are isomorphic as an
`R`-module to the Čech `H⁰` of `M` for `K`.

Proof (namespace `AC3Aux`). Restriction to the members defines `toH0 : Γ(M, ⊤) → H⁰` (`res_mem_H0`).
It is injective and surjective by the sheaf property of `M` (`shf`): degree-`0` cocycles are families
agreeing on pairwise intersections (using the `1`-tuples `chain1`), which glue uniquely
(`toH0_injective`, `toH0_surjective`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.chain0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.idx0_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.U_le_inter_chain0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.inter_le_U`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.chain1`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.inf_le_inter_chain1`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.F`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.res_mem_H0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.toH0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.toH0_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.shf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.toH0_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux.toH0_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library).
Other imports: `Mathlib`.
