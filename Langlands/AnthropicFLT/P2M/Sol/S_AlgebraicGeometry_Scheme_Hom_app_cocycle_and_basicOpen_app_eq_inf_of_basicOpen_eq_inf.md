# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.lean` (SHA-256 `4e34adc9c2aa43a08e8e549dda047b854efb80d34c4ee1337c17c6c9b6546d18`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`.

Statement. `AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`: let
`f : X ⟶ Z` be a morphism of schemes and let `w i j ∈ Γ(Z, V i)` (`i j : Fin r`) satisfy `w i i = 1`,
the cocycle identity `w i k = w i j * w j k` after restriction to `V i ⊓ V j`, and
`Z.basicOpen (w i j) = V i ⊓ V j`. Then the pullbacks `f.app (V i) (w i j)` satisfy the same three
identities for the opens `f ⁻¹ᵁ V i` of `X`.

Proof. Pullback of sections commutes with restriction (naturality of `f.app`, the local lemma `nat`);
the identities then follow from `map_one`, `map_mul` and `Scheme.preimage_basicOpen`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
