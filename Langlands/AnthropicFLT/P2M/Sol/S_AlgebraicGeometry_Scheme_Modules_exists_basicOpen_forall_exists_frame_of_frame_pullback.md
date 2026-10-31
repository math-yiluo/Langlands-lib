# Spreading a local frame from a field-valued fibre to a basic open neighbourhood

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u`, `f : X ⟶ Spec R` a
universally closed morphism, `M` an invertible sheaf of modules on `X` (in
the sense of the port's `Scheme.Modules.IsInvertible`) and
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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

By `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame`
it suffices to find a frame near each point `x` with `f x = 𝔭`. The point
`𝔭` is the image of the unique point of `Spec K`, because the kernel of
`R → K` is `𝔭`. So `Scheme.Pullback.exists_preimage_pullback` gives a point
`z ∈ X_K` with `p z = x`. The hypothesis gives an index `i` and a frame of
`p^* M` near `z` from the pullback of `m_i`, and
`AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback` descends it
to a frame of `M` near `p z = x` from `m_i`.
