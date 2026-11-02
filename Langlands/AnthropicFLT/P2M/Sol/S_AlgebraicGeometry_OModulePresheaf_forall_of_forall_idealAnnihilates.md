# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.P2mFiltQ (isLocallyNoetherian)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line None, line 89 here): `haveI : IsLocallyNoetherian V := isLocallyNoetherian π` is replaced by `haveI : IsLocallyNoetherian V := _root_.P2mFiltQ.isLocallyNoetherian π`. FLT `p2m_export "P2mFiltQ" "isLocallyNoetherian"` aliases the private declaration(s) `_root_.P2mFiltQ.`, `_root_.isLocallyNoetherian.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `P2mFiltQ` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- Port edit replacing a `P2M.Util` alias (FLT line None, line 156 here): `haveI : IsLocallyNoetherian V := isLocallyNoetherian π` is replaced by `haveI : IsLocallyNoetherian V := _root_.P2mFiltQ.isLocallyNoetherian π`. FLT `p2m_export "P2mFiltQ" "isLocallyNoetherian"` aliases the private declaration(s) `_root_.P2mFiltQ.`, `_root_.isLocallyNoetherian.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `P2mFiltQ` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates`. Statement. `AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates`: for `π : V ⟶ Spec R` proper
over a noetherian ring, a closed set `Y` and a predicate `Q` on FLT presheaves of modules that holds for
zero presheaves and satisfies two-out-of-three on short exact sequences of coherent quasi-coherent
presheaves: if `Q` holds for every coherent quasi-coherent presheaf supported in `Y` and annihilated
by the vanishing ideal of `Y`, then it holds for every coherent quasi-coherent presheaf supported in
`Y`.

Proof (namespace `P2mFiltQ`). `V` is locally noetherian and quasi-compact (properness over a
noetherian ring). The zero presheaf and the presheaves `Iᵏ F` (`idealPow`) are coherent
(`isCoherent_zero`, `isCoherent_idealPow`). Section `Uniform`: for `F` supported in `Y`, some power
`I_Y^N F` vanishes on every affine open (`exists_forall_subsingleton_idealPow`: locally by the
support condition and quasi-coherence, uniformly by quasi-compactness). Section `Main`: induction along
the filtration `F ⊇ I F ⊇ … ⊇ I^N F = 0`, whose successive quotients are annihilated by `I`, using the
two-out-of-three property.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private theorem `P2mFiltQ.isLocallyNoetherian`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.compactSpace`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.isCoherent_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.isQuasicoherent_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.isCoherent_idealPow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.subsingleton_basicOpen_of_subsingleton`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.exists_forall_subsingleton_idealPow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.P2mFiltQ.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero` (same contribution).
Other imports: `Mathlib`.
