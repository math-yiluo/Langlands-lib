# An invertible sheaf on an integral scheme with constant global functions is trivial if it and its dual have nonzero sections

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero` states under its FLT name.

## Statement

Let `Y` be an integral scheme on which every nonzero global function is a
unit, and `P` an invertible sheaf of modules on `Y` (the port's
`Scheme.Modules.IsInvertible`). Write `dual P` for the internal hom from `P`
to the structure sheaf. If `P` has a nonzero global section and `dual P` has a
nonzero global section, then `P` is isomorphic to the monoidal unit (the
structure sheaf) of `Y.Modules`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped; the `p2m_alias` command is dropped, since dot notation already resolves to the same declaration. No declaration, statement or proof step changed;

## Proof outline

1. Local frames. Every point has an open neighbourhood `U` with a frame of `P`
   on `U` (a section `f` such that `g ↦ g • f|W` is bijective for every open
   `W ≤ U`; `IsFrameOn`), namely the inverse image of `1` under a local
   trivialization. The comparison between the pullback along `U.ι` and the
   restriction (`restrictFunctor'`, `Scheme.Modules.restrictFunctorIsoPullback`)
   is as in `Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit`.
2. Injectivity of restriction. On an integral scheme, restriction of functions
   to a nonempty smaller open is injective (`map_injective_of_isIntegral`), and
   any two nonempty opens meet. Using local frames, the same holds for
   sections of `P` (`map_injective_of_isInvertible`), and a morphism
   `φ : P ⟶ 𝒪_Y` that vanishes on a frame over a nonempty open is zero
   (`hom_unit_eq_zero_of_app_frame_eq_zero`).
3. The two sections as morphisms. The nonzero global section `s` of `P` gives a
   nonzero morphism `σ : 𝒪_Y ⟶ P`, `g ↦ g • s`
   (`SheafOfModules.unitHomEquiv`). The nonzero global section `s'` of
   `dual P` gives, by uncurrying, a nonzero morphism `φ : P ⟶ 𝒪_Y`.
4. The global function `a = φ(s)` is nonzero. On a frame `f` over a nonempty
   `U`, write `s|U = b • f` and `φ(f) = b'`, so `a|U = b * b'`. If `a = 0`, the
   ring of functions on `U` is a domain, so `b = 0` or `b' = 0`. In the first
   case `s|U = 0`, hence `s = 0` by step 2; in the second case `φ = 0` by
   step 2. Both are excluded.
5. So `a` is a unit, and for every frame `f` on `U` the coefficient `b` with
   `s|U = b • f` divides the unit `a|U`, hence is a unit. Then on each open
   `W ≤ U`, `σ` is multiplication by the unit `b|W` followed by the bijection
   `g ↦ g • f|W`, so its component on `W` is bijective. By
   `Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top` (in this port)
   applied to the cover by frame domains, `σ` is an isomorphism, and its
   inverse is the required isomorphism.
