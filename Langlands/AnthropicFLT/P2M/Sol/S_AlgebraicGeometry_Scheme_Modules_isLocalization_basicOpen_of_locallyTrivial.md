# Sections of a locally trivial module localize on basic opens of an affine open

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial` states under its FLT name.

## Statement

Let `X` be a scheme and `M` a sheaf of modules on `X` that is locally
trivial: every point has an open neighbourhood `V` such that the pullback of
`M` along `V.ι` is isomorphic to the structure sheaf of `V`. Let `U` be an
affine open of `X` and `f ∈ Γ(X, U)`. Then the restriction from `U` to the
basic open `X_f` behaves like the localization at the powers of `f`:

- every section `x` of `M` over `X_f` becomes, after multiplication by the
  restriction of some power `f ^ n`, the restriction of a section over `U`;
- every section over `U` whose restriction to `X_f` is zero is killed by some
  power `f ^ n`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

1. Trivial case. Suppose `W ≤ V` is an affine open and `e : M|V ≅ 𝒪_V` a
   trivialization (the pullback along `V.ι` is identified with the restriction
   by `Scheme.Modules.restrictFunctorIsoPullback`). Then `e` induces, for every
   open `W' ≤ V`, an isomorphism `ψ` from the sections of `M` over `W'` to
   `Γ(X, W')`, which is linear over functions and commutes with restriction
   (via the image of `V.ι⁻¹ W'` under `V.ι`, which is `W'`). So the
   localization property of `M` on `W` at `g ∈ Γ(X, W)` is the corresponding
   property of the structure sheaf, which holds because `Γ(X, X_g)` is the
   localization of `Γ(X, W)` at `g` for affine `W`
   (`IsAffineOpen.isLocalization_basicOpen`, `IsLocalization.surj`,
   `IsLocalization.map_eq_zero_iff`).
2. Finite cover. For each point `x` of `U` choose a trivializing open
   `V ∋ x` and a function `h` on `U` with `x ∈ X_h ≤ V`
   (`IsAffineOpen.exists_basicOpen_le`). Since `U` is quasi-compact, finitely
   many of these basic opens cover `U`. Each `X_h` is affine, and so is each
   intersection `X_h ∩ X_{h'}`, the basic open of the restriction of `h'` in
   the affine `X_h` (`Scheme.basicOpen_res`); both lie in a trivializing
   open. By step 1, the localization property holds for all functions on
   these opens.
3. `Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover` (in
   this port) glues these to the property on `U` at `f`.
