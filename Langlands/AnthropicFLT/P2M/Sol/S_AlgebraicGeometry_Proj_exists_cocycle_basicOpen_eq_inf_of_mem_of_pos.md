# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.lean` (SHA-256 `beeb2b54ee39c8209947876d08d7a48dbfe343186d5ed2cbbcb31d8a4a85505e`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`.

Statement. `AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`: let `𝒜` be an
`ℕ`-graded ring and let `F i ∈ 𝒜 d` (`i : Fin r`) be homogeneous of one positive degree `d`. Then the
opens `D₊(F i)` of `Proj 𝒜` are affine, and there are sections `w i j` of `Proj 𝒜` over `D₊(F i)` with
`w i i = 1`, `w i k = w i j * w j k` after restriction to `D₊(F i) ⊓ D₊(F j)`, and
`(Proj 𝒜).basicOpen (w i j) = D₊(F i) ⊓ D₊(F j)`; namely `w i j = F j / F i`.

Proof. `w i j` is the image under `Proj.awayToSection` of the degree-zero fraction `F j / F i`
(`HomogeneousLocalization.Away.mk`). `F i / F i = 1` gives `w i i = 1`. For the cocycle identity, the
restrictions to `D₊(F i * F j) = D₊(F i) ⊓ D₊(F j)` (`Proj.basicOpen_mul`) are computed in the
localization at `F i * F j` by `Proj.awayMap_awayToSection`, where they are an identity of fractions.
For the basic opens: through `fromSpec` of the affine open `D₊(F i)`, the preimage of `D₊(F j)` is the
basic open of `(F j / F i) ^ d` (`Proj.awayι_preimage_basicOpen`), which is the basic open of `F j / F i`;
its image is `D₊(F i) ⊓ D₊(F j)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
