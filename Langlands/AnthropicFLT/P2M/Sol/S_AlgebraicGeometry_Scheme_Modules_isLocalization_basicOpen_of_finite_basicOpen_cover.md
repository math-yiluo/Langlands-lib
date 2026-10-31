# Localization of sections on basic opens is local for a finite cover

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `D_i = X_{h_i}` for the members of the cover and `W_i = D_i ∩ X_f`, the
basic open of the restriction of `f` to `D_i` (`Scheme.basicOpen_res`); the
`W_i` cover `X_f`.

- Kernel condition. If `y ∈ Γ(M, U)` vanishes on `X_f`, then its restriction
  to each `D_i` vanishes on `W_i`, so it is killed by a power `f ^ {n_i}` on
  `D_i`. With `n` the maximum of the finitely many `n_i`, `f ^ n • y` vanishes
  on every `D_i`, hence is zero because `M` is a sheaf.
- Surjectivity up to powers. Let `x ∈ Γ(M, X_f)`. On each `D_i`, the
  hypothesis gives `n_i` and `y_i ∈ Γ(M, D_i)` with `y_i|W_i = f ^ {n_i} • x|W_i`;
  multiplying by further powers of `f`, one may use a common exponent `n`. On
  an overlap `D_i ∩ D_j` the difference of the restrictions of `y_i` and
  `y_j` vanishes on the basic open of `f` there, so by the hypothesis on
  `D_i ∩ D_j` it is killed by a power of `f`; let `m` be a common exponent.
  The sections `f ^ m • y_i` are then compatible on overlaps and glue to
  `y ∈ Γ(M, U)` (`TopCat.Sheaf.existsUnique_gluing'`). Its restriction to
  `X_f` agrees with `f ^ {m + n} • x` on every `W_i`, hence on `X_f`.
