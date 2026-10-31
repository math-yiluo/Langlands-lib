# Finite Čech cohomology of coherent sheaves, reduced to integral closed subschemes (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` proper, and `K` an ordered affine cover of `V`.
Assume `hInt`: for every nonempty closed `Z₀ ⊆ V` whose reduced subscheme is integral, if every coherent
quasi-coherent presheaf of modules over `π` supported in a closed set strictly smaller than `Z₀` has finitely
generated Čech cohomology for `K`, then so does the pushforward of the structure sheaf of that subscheme.
Then for every closed `Y` and every coherent, quasi-coherent presheaf of modules `F` over `π` supported in
`Y`, `F` has finitely generated Čech cohomology for `K` (`CechFinite K`). The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral` and proves it from `solution`.

## Proof outline

The helpers are in the namespace `…AlgebraicGeometry.OModulePresheaf.Driver`: `isNoetherian_of_isProper`
(`V` is noetherian), and `cechFinite_of_supportedIn_empty` (a presheaf supported in the empty set vanishes
on every affine intersection, so all its cochains are zero).

The proof is noetherian induction on the closed set `Y` (well-founded, since `V` is noetherian).

1. If `Y` is empty, use `cechFinite_of_supportedIn_empty`.
2. Otherwise, by the FLT theorem `OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot` it suffices
   to treat the graded pieces `I_Y^k F / I_Y^{k+1} F`. They are coherent, quasi-coherent, supported in `Y`
   and annihilated by `I_Y` (`isCoherent_idealPowQuot`, `isQuasicoherent_idealPowQuot`,
   `supportedIn_idealPowQuot`, `idealAnnihilates_idealPowQuot`).
3. For such an `F'`, the FLT theorem `OModulePresheaf.hasDevissageStep` gives a short exact sequence
   `0 → i_*H → F' → G₃` (on affine opens) with `G₃` supported in a smaller `Z₁`. So `G₃` is handled by the
   induction hypothesis. If the integral closed `Z₀` of the step is strictly smaller than `Y`, `i_*H` is
   handled by the induction hypothesis too. If `Z₀ = Y`, use the FLT theorem
   `OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih` with `hInt`. Finally
   `OModulePresheaf.cechFinite_of_affSES_mid` gives finiteness for `F'`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` and of
  the theorem modules `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep`,
  `…_cechFinite_pushforward_of_isIntegral_of_ih`, `…_cechFinite_of_forall_cechFinite_idealPowQuot`,
  `…_isCoherent_idealPowQuot`, `…_isQuasicoherent_idealPowQuot`, `…_supportedIn_idealPowQuot` and
  `…_cechFinite_of_affSES_mid` are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.
