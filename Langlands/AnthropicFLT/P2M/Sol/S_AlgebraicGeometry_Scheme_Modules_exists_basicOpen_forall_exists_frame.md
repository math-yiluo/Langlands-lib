# Spreading a local frame from a fibre to a basic open neighbourhood

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

The set `W` of points admitting a frame from `m` is open: the open `U` in
the definition witnesses the condition for each of its points. Since `f` is
universally closed it is a closed map, so `Z = f(X \ W)` is closed in
`Spec R`. By hypothesis no point over `𝔭` lies outside `W`, so `𝔭 ∉ Z`.
Basic opens form a basis of `Spec R`
(`PrimeSpectrum.isTopologicalBasis_basic_opens`), so some `D(g)` contains `𝔭`
and misses `Z`. Then `g ∉ 𝔭`, and a point `x` over `D(g)` outside `W`
would put `f x` in `Z ∩ D(g) = ∅`.
