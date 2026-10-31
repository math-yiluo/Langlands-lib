# Sections of a locally trivial module over an affine open are projective

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.projective_sections_of_locallyTrivial`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` states under its FLT name.

## Statement

Let `X` be a scheme and `M` a sheaf of modules on `X` that is locally
trivial: every point has an open neighbourhood `V` such that the pullback of
`M` along `V.ι` is isomorphic to the structure sheaf of `V`. Then for every
affine open `U` of `X`, the module of sections `Γ(M, U)` is a projective
module over the ring `Γ(X, U)`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `A = Γ(X, U)` and `P = Γ(M, U)`. The module `P` is finite over `A` by
`Scheme.Modules.finite_sections_of_locallyTrivial` (in this port).

1. Local identification. Let `f ∈ A` with `X_f` inside an open `V` on which
   `M` is trivial, `e : M|V ≅ 𝒪_V`. As in
   `Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`, `e` induces an
   isomorphism `ψ` from sections of `M` over `X_f` to `Γ(X, X_f)`, linear over
   functions and compatible with restriction. The `A`-linear map
   `P → Γ(X, X_f)`, `m ↦ ψ(m|X_f)`, is a localization of `P` at the powers of
   `f` (`IsLocalizedModule`): `f` acts invertibly on `Γ(X, X_f)` because
   `Γ(X, X_f)` is the localization of `A` at `f`, and surjectivity up to
   powers and the kernel condition are
   `Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial` (in this port).
   So `P_f` is free of rank one over `A_f`.
2. The set `s` of such `f` generates the unit ideal of `A`: every point of the
   affine open `U` has a basic open neighbourhood inside a trivializing open
   (`IsAffineOpen.exists_basicOpen_le`, `IsAffineOpen.self_le_iSup_basicOpen_iff`).
3. Flatness is local on a family generating the unit ideal
   (`Module.flat_of_isLocalized_span`), and each `P_f ≅ A_f` is flat over `A`,
   so `P` is flat.
4. Rank one at every prime `p`: some `f ∈ s` is not in `p`, so `p` comes from
   a prime of `A_f` (`PrimeSpectrum.localization_away_comap_range`); the
   localization of step 1 is a base change (`IsLocalizedModule.isBaseChange`),
   and `rankAtStalk` is invariant under base change and equals one for the
   free module `A_f`.
5. By `Module.finitePresentation_of_rankAtStalk_eq` (in this port), the finite
   flat module `P` of constant rank one is finitely presented, and a finitely
   presented flat module is projective
   (`Module.Flat.projective_of_finitePresentation`).
