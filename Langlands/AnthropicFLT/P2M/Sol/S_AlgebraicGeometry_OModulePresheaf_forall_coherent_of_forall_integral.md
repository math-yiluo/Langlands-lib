# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral`. Statement. `AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral` (dévissage): let
`π : V ⟶ Spec R` be proper over a noetherian ring and `Q` a predicate on pairs (closed set, FLT
presheaf of modules) that holds for presheaves with zero sections on affine opens, is monotone in the
closed set, satisfies the two-out-of-three property on short exact sequences of coherent
quasi-coherent presheaves, and holds for `𝒪_{Z₀}` (the pushforward of the structure sheaf of the
reduced subscheme) whenever `Z₀` is nonempty with integral reduced subscheme and `Q` holds for all
coherent quasi-coherent presheaves supported in proper closed subsets of `Z₀`. Then `Q Y F` holds for
every coherent quasi-coherent `F` supported in `Y`.

Proof (namespace `P2mDevissageDriver`). `V` is noetherian (`isNoetherian`), so closed sets satisfy
well-founded induction. `step`: assuming `Q` below `Y`, a coherent quasi-coherent `F` supported in `Y`
is handled by the ported filtration theorem `OModulePresheaf.forall_of_forall_idealAnnihilates`
(reduction to presheaves killed by the ideal of `Y`) and the ported
`OModulePresheaf.forall_pushforward_of_isIntegral` on each irreducible component with integral
reduced structure (decomposing `Y` into irreducible components and using monotonicity and extensions);
`main` is the well-founded induction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.P2mDevissageDriver.isNoetherian`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.P2mDevissageDriver.step`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.P2mDevissageDriver.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral` (same contribution).
Other imports: `Mathlib`.
