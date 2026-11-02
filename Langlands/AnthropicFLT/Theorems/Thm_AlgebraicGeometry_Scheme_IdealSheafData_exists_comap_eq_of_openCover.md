# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution 𝒰 I hI`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover` (gluing ideal sheaves): for an open
cover `𝒰` of `X` and ideal sheaves `Iᵢ` on the members whose pullbacks agree on all overlaps (for every
pair of maps `a, b` from a scheme with `a ≫ 𝒰.f i = b ≫ 𝒰.f j`), there is an ideal sheaf `I₀` on `X`
restricting to `Iᵢ` on each member.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover` (same contribution).
Other imports: `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, `Mathlib.AlgebraicGeometry.Cover.Open`.
