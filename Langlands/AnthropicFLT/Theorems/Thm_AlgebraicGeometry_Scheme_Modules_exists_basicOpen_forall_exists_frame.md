# Spreading a local frame from a fibre to a basic open neighbourhood

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame` proves the theorem `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame`.

## Statement

Let `R` be a commutative ring in universe `u`, `f : X ⟶ Spec R` a
universally closed morphism, `M` a sheaf of modules on `X`, `m : ι → Γ(M, ⊤)`
a finite family of global sections and `𝔭` a prime of `R`. Say that `x ∈ X`
admits a frame from `m` if there are an index `i` and an open `U ∋ x` such
that, for every open `V ≤ U`, the map `Γ(X, V) → Γ(M, V)`, `g ↦ g • m_i|_V`,
is bijective; so `m_i` restricts to a basis of `M` near `x`. If every point
of `X` lying over `𝔭` (that is, with `f x = 𝔭`) admits a frame from `m`,
then there is `g ∈ R` with `g ∉ 𝔭` such that every point `x` with
`f x ∈ D(g)` admits a frame from `m`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame`, which has the same statement. The Markdown of that module outlines the argument.
