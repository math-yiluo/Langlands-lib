# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation`. Statement. `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_functionField_presentation`: an invertible module `M` on
an integral scheme `X` embeds into the function field: there are additive maps `φ U : Γ(M, U) → K(X)`,
compatible with restriction to nonempty opens, semilinear over `Γ(X, U) → K(X)`, and injective on
nonempty opens.

Proof. Section `Coord`: on a trivializing open `W`, a trivialization gives coordinates `coord : Γ(M, U) →
Γ(X, U)` for `U ⊆ W`, injective and compatible with restriction and scalars. Fix one trivializing open `W₀`
(nonempty); for any `U`, `φ U m` is the germ at the generic point of the coordinate of the restriction of
`m` to `U ∩ W₀` (sections `InW`, `Generic`, `Pres`), well defined since the generic point lies in every
nonempty open; injectivity (section `Inj`) holds because a section of a locally free module on an integral
scheme vanishing at the generic point vanishes (`eq_zero_of_res_eq_zero`, using
`restrictIsoOfPullbackIso` on the trivializing opens).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.trivApp`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.trivApp_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.coord`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.coord_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.trivApp_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.coord_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.map_trivApp`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.map_coord`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.coord_smul`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.inW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.inW_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.inW_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.mem_inW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.preimage_mono_of_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.inW_mono`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.genericPoint_mem`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.genericPoint_mem_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.eq_zero_of_res_eq_zero`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.resIn`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.pres`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.pres_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.pres_natural`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.pres_smul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.restrictIsoOfPullbackIso`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.resIn_eq_zero_of_resIn_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.eq_zero_of_resIn_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.P2mKPresSol.main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library).
Other imports: `Mathlib`.
