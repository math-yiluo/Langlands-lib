# A module on an affine scheme whose sections localize on basic opens is the sheaf of its global sections

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen` states under its FLT name.

## Statement

Let `R` be a commutative ring and `M` a sheaf of modules on `Spec R`. Suppose
that for every global function `g` of `Spec R`, the restriction from global
sections of `M` to sections over the basic open `D(g)` behaves like the
localization at the powers of `g`, in the following explicit form:

- every section `x` over `D(g)` becomes, after multiplication by the
  restriction of some power `g ^ n`, the restriction of a global section;
- every global section whose restriction to `D(g)` is zero is killed by some
  power `g ^ n`.

Then the canonical morphism `M.fromTildeΓ` from the sheaf associated with the
`R`-module of global sections to `M` is an isomorphism.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

By `Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule` (in this
port), it suffices that for every `f ∈ R` the restriction map from global
sections to sections over the basic open `D(f)` of the prime spectrum is a
localization of `R`-modules at the powers of `f` (`IsLocalizedModule`). Apply
the hypothesis to the global function `g` corresponding to `f` under
`Scheme.ΓSpecIso`; its scheme-theoretic basic open is `D(f)`
(`basicOpen_eq_of_affine`). The three conditions of
`IsLocalizedModule.mk` then hold:

- `f` acts invertibly on the sections over `D(f)`
  (`Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`), hence so does
  every power;
- surjectivity up to powers and the kernel condition are the two
  hypotheses, after rewriting the `R`-module structure on sections as
  multiplication by the restriction of the corresponding global function.
