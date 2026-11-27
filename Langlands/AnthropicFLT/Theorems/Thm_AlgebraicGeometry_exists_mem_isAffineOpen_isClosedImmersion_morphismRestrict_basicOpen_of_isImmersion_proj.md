# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.lean` (SHA-256 `70ee227d2e35e7899a8360cf1019b85987308a3adc2c5fd7092ef832d832010a`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution 𝒜 ι S`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`:
let `𝒜` be an `ℕ`-graded ring (`GradedRing 𝒜`, with underlying ring `A`), let `ι : X ⟶ Proj 𝒜` be an
immersion and let `S` be a finite set of points of `X`. Then there is a homogeneous element `F ∈ 𝒜 d` of
positive degree `d` such that the preimage `ι ⁻¹ᵁ D₊(F)` contains `S` and is affine, and the restriction
`ι ∣_ D₊(F)` is a closed immersion.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`.
Other imports: `Langlands.MathlibBase`.
