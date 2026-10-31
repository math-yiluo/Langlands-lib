# A global section that is locally a frame is a frame

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul` states under its FLT name.

## Statement

Let `X` be a scheme, `M` a sheaf of modules on `X`, `σ` a global section of
`M` and `V` an open of `X`. For an open `W`, write `σ|W` for the restriction
of `σ` to `W`. Suppose every point `x` of `V` has an open neighbourhood `U`
such that for every open `W ≤ U` the map `Γ(X, W) → Γ(M, W)`,
`g ↦ g • σ|W`, is bijective. Then the map `Γ(X, V) → Γ(M, V)`,
`g ↦ g • σ|V`, is bijective. So the property "`σ` is a frame of `M` on all
smaller opens" is local on `V`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

Choose for each point `x` of `V` a neighbourhood `U x` as in the hypothesis,
and put `W x = V ⊓ U x`; the opens `W x` cover `V`. Restriction commutes with
the scalar action: the restriction of `g • σ|W` to `W' ≤ W` is
`g|W' • σ|W'` (`Scheme.Modules.map_smul`).

- Injectivity: if `g₁ • σ|V = g₂ • σ|V`, then restricting to each `W x` gives
  `g₁|W x • σ|W x = g₂|W x • σ|W x`, so `g₁|W x = g₂|W x` by the hypothesis
  on `W x ≤ U x`. Since the structure sheaf is a sheaf, `g₁ = g₂`
  (`TopCat.Sheaf.eq_of_locally_eq'`).
- Surjectivity: given `s ∈ Γ(M, V)`, the hypothesis gives for each `x` a
  unique `g x ∈ Γ(X, W x)` with `g x • σ|W x = s|W x`. On an overlap
  `W x ⊓ W y`, which lies in `U x`, both restrictions of `g x` and `g y`
  multiply `σ` to the restriction of `s`, so they agree by injectivity
  there. The family glues to `g ∈ Γ(X, V)`
  (`TopCat.Sheaf.existsUnique_gluing'`), and `g • σ|V` and `s` agree on every
  `W x`, hence are equal because `M` is a sheaf of abelian groups.
