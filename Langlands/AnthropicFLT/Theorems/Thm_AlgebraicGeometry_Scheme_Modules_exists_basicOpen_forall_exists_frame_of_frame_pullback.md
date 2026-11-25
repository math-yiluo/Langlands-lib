# Spreading a local frame from a field-valued fibre to a basic open neighbourhood

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback` proves the theorem `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback`.

## Statement

Let `R` be a commutative ring in universe `u`, `f : X ⟶ Spec R` a
universally closed morphism, `M` an invertible sheaf of modules on `X` (in
the sense of the port's `Scheme.Modules.IsInvertibleFLT`) and
`m : ι → Γ(M, ⊤)` a finite family of global sections. Let `K` be a field
with an `R`-algebra structure whose kernel is the prime `𝔭` of `R`, and let
`X_K = X ×_{Spec R} Spec K` with first projection `p : X_K ⟶ X`. Suppose
that every point of `X_K` admits a frame from the pulled-back sections: for
each `z ∈ X_K` there are `i` and an open `U' ∋ z` such that, for every open
`V' ≤ U'`, multiplication `g ↦ g • (η m_i)|_{V'}` is a bijection from
`Γ(X_K, V')` onto the sections of `p^* M` over `V'`, where `η` is the unit
`M ⟶ p_* p^* M`. Then there is `g ∈ R` with `g ∉ 𝔭` such that every point
`x ∈ X` with `f x ∈ D(g)` admits a frame from `m` on `X` (in the sense of
`exists_basicOpen_forall_exists_frame`).

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's, apart from the renames described under “Names changed by the Library” below. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`);
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback`, which has the same statement. The Markdown of that module outlines the argument.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible` are uses of `IsInvertibleFLT` now.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
