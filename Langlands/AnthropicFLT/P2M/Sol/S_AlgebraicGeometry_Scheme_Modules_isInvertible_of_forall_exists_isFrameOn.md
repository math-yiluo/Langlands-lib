# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands.
  - FLT line 14: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry`.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

`solution` states: a sheaf of modules `M` on a scheme `X` is invertible in FLT's sense
(`Scheme.Modules.IsInvertible`, from the C1 port `Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`:
every point has an open neighbourhood `U` with `(Scheme.Modules.pullback U.ι).obj M ≅ 𝒪_U`) as soon as every
point `x` has an open `U ∋ x` and a section `s : Γ(M, U)` with `IsFrameOn s U`. Here `IsFrameOn s V` (C1 port
`Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`) means that for every open `W ⊆ U` with `W ⊆ V`
the map `Γ(X, W) → Γ(M, W)`, `g ↦ g • s|_W`, is bijective.

Proof as implemented: for a point `x` take the given `U` and `s`; the C1 lemma
`IsFrameOn.nonempty_pullback_iso_unit` (applied with `V = U`) gives the required isomorphism with `𝒪_U`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit`.
