# Sections of a locally trivial module over an affine open are finitely generated

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial` states under its FLT name.

## Statement

Let `X` be a scheme and `M` a sheaf of modules on `X` that is locally
trivial: every point has an open neighbourhood `V` such that the pullback of
`M` along `V.ι` is isomorphic to the structure sheaf of `V`. Then for every
affine open `U` of `X`, the module of sections `Γ(M, U)` is finitely
generated over the ring `Γ(X, U)`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `A = Γ(X, U)`.

1. Cover. For each point of `U` choose a trivializing open `V`,
   `e : M|V ≅ 𝒪_V`, and `h ∈ A` with the point in `X_h ≤ V`
   (`IsAffineOpen.exists_basicOpen_le`). As `U` is quasi-compact, finitely
   many `h_1, …, h_k` suffice, and they generate the unit ideal of `A`
   (`IsAffineOpen.self_le_iSup_basicOpen_iff`).
2. Local generators. On `X_{h_i}`, the trivialization identifies sections of
   `M` with functions, linearly and compatibly with restriction (the map `ψ`
   of `Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`); let `u_i`
   be the section corresponding to `1`, so every section `z` over `X_{h_i}`
   equals `ψ(z) • u_i`. By
   `Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial` (in this port),
   `h_i ^ {n_i} • u_i` is the restriction of a section `y_i ∈ Γ(M, U)`.
3. Every `m ∈ Γ(M, U)` satisfies `h_i ^ {e_i} • m ∈ A • y_i` for some `e_i`:
   the function `ψ(m|X_{h_i})` is `b / h_i ^ k` for some `b ∈ A`
   (`IsLocalization.surj`), so `h_i ^ {k + n_i} • m - b • y_i` vanishes on
   `X_{h_i}`, hence is killed by a power of `h_i` (the kernel half of the same
   theorem).
4. Let `N` be a common exponent. The powers `h_i ^ N` still generate the unit
   ideal (`Ideal.span_pow_eq_top`); writing `1 = Σ a_i h_i ^ N` gives
   `m = Σ a_i h_i ^ N • m` in the span of `y_1, …, y_k`. Hence these finitely
   many sections generate `Γ(M, U)`.
