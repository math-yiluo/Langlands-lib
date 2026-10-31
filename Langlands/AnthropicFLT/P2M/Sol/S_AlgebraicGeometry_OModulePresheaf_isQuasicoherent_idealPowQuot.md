# The graded pieces of the ideal filtration of a quasi-coherent sheaf are quasi-coherent (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R`, `I` an ideal sheaf on `V`, and `F` a
quasi-coherent presheaf of modules over `π`. Then for every `k` the graded piece `I^k F / I^{k+1} F`
(`OModulePresheaf.idealPowQuot π I F k`) is quasi-coherent. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot` states this as
`AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.G4T`. Fix an affine open `U` and
`f ∈ Γ(V, U)`.

1. `isQuasicoherent_idealPow`: `I^k F` is quasi-coherent. On `D(f)` the ideal `I(D(f))^k` is the extension
   of `I(U)^k` along the localization `Γ(V, U) → Γ(V, D(f))`. An element `a · z` of `I^k F(D(f))`, with
   `a = b / f^m` for `b ∈ I(U)^k` and `z = w₀ / f^{n₀}` by quasi-coherence of `F`, is the restriction of
   `b · w₀ ∈ I^k F(U)` divided by `f^{m+n₀}`. Sums are handled by a common power of `f`. The vanishing
   condition is inherited from `F`.
2. `isQuasicoherent_idealPowQuot`: for the quotient, lift a section over `D(f)` to `I^k F(D(f))`, apply
   step 1, and project. If a section `y'` of `I^k F(U)` becomes zero in the quotient over `D(f)`, its
   restriction lies in `I^{k+1} F(D(f))`. Apply step 1 to `I^{k+1} F` to find `z` over `U`, then the
   vanishing condition for `I^k F` to the difference. This shows that `f^{m+n} y'` lies in `I^{k+1} F(U)`.
   The short exact sequence `idealPowSES` organizes these lifts and projections.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` is renamed
  to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
