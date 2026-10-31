# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 13: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry N.AlgebraicGeometry"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 18: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits`.
  - FLT line 23: `p2m_export "PresheafOfModules" "…"` with 13 names becomes `export _root_.PresheafOfModules (…)` with the same names.
  - FLT line 24: `p2m_open "PresheafOfModules"` becomes `open _root_.PresheafOfModules`.
  - FLT line 44: `p2m_export "AlgebraicGeometry" "…"` with 9 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 46: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 15 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 48: `p2m_export "AlgebraicGeometry.Scheme.Modules" "…"` with 10 names becomes `export _root_.AlgebraicGeometry.Scheme.Modules (…)` with the same names.
  - FLT line 49: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 144: `p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible (pullback)`.
  - FLT line 145: `p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsInvertible" in` becomes `open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in`; both only activate the scoped declarations of the namespace for the next command.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

`solution` states: if `M` is invertible in FLT's sense, every point `x` has an open neighbourhood `U` and a
section `s : Γ(M, U)` with `IsFrameOn s U`; this is the converse of
`isInvertible_of_forall_exists_isFrameOn`.

Proof as implemented: take `U ∋ x` and an isomorphism `(Scheme.Modules.pullback U.ι).obj M ≅ 𝒪_U` from
invertibility. The file identifies restriction along `U.ι` with a pushforward functor `restrictFunctor' U`
(`restrictFunctor'_eq`, then Mathlib's `Scheme.Modules.restrictFunctorIsoPullback`), so the trivialization
becomes `e : (restrictFunctor' U).obj M ≅ 𝒪_U`. For an open `W` of the scheme `U`, `gen₀` is the image of
`1` under `e⁻¹` in the sections of `M` over the image `U.ι ''ᵁ W`; since `e⁻¹` is linear and bijective,
`b ↦ b • gen₀ W` is bijective (`gen₀_bijective`), and the `gen₀` are compatible with restriction (`gen₀_map`).
Transporting along the equality `U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V` for `V ⊆ U` (`image_preimage_of_le`,
`bijective_smul_map_eqToHom`) gives a compatible family of generators over all opens below `U`
(`trivializationBelow`, a `PresheafOfModules.FrameBridge.TrivializationBelow`). Its member over `U` itself is
the required frame: its restriction to any `W ⊆ U` is the generator over `W`, for which `g ↦ g • gen` is
bijective.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- structure `TrivializationBelow`
- def `restrictRingCatSheafHom`
- def `restrictFunctor'`
- lemma `restrictFunctor'_eq`
- def `restrictFunctor'IsoPullback`
- lemma `image_preimage_of_le`
- def `gen₀`
- lemma `gen₀_spec`
- lemma `gen₀_bijective`
- lemma `gen₀_map`
- lemma `bijective_smul_map_eqToHom`
- def `trivializationBelow`
- theorem `IsInvertible.exists_isFrameOn'`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`.
