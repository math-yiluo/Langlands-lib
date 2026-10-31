# Localization of sections on basic opens is local for a finite cover

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover` proves the theorem `AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover`.

## Statement

Let `X` be a scheme and `M` a sheaf of modules on `X`. For an open `V` and a
function `g ∈ Γ(X, V)`, say that `M` *localizes at `g` on `V`* if

- every section `x` of `M` over the basic open `X_g ⊆ V` becomes, after
  multiplication by the restriction of some power `g ^ n`, the restriction of
  a section over `V`; and
- every section over `V` whose restriction to `X_g` is zero is killed by some
  power `g ^ n`.

Let `U` be an affine open of `X` and `s` a finite set of functions on `U`
whose basic opens `X_h` (`h ∈ s`) cover `U`. Suppose that `M` localizes at
every function on `X_h` for every `h ∈ s`, and at every function on
`X_h ∩ X_{h'}` for all `h, h' ∈ s`. Then `M` localizes at every `f ∈ Γ(X, U)`
on `U`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover`, which has the same statement. The Markdown of that module outlines the argument.
