# A generator of the kernel of a two-term complex with free rank-one H⁰ is unimodular

`Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv` proves the theorem `P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution`. Its statement is that of `CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv`, which `Langlands.AnthropicFLT.Theorems.Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv` states under its FLT name.

## Statement

Let `R` be a commutative ring and `G` a two-term complex over `R` (the FLT
structure `CoherentBaseChange.TwoTermComplex`: a linear map `d : C0 → C1`
between finite free `R`-modules). For an `R`-algebra `A`, `G.H0 A` is the
kernel of the base change `A ⊗ d`. Let `g₀ ∈ C0` be such that every element
of `ker d` is an `R`-multiple of `g₀`, and suppose that for every
`R`-algebra `C` (in universe `u`) the `C`-module `G.H0 C` is isomorphic to
`C`. Then for every nontrivial `R`-algebra `C`, the element `1 ⊗ g₀` of
`C ⊗[R] C0` is nonzero.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Suppose `1 ⊗ g₀ = 0` in `C ⊗ C0`; then `m ⊗ g₀ = m • (1 ⊗ g₀) = 0` for every
`m ∈ C`. The proof shows that then `C` is a subsingleton, contradicting
nontriviality. It uses the square-zero extension `E = R ⊕ C`
(`TrivSqZeroExt R C`, with `C` viewed as an `R`-module), which is an
`R`-algebra, so `G.H0 E ≅ E` by hypothesis.

1. Every `inr m`, `m ∈ C`, kills `G.H0 E`. Let `k ∈ G.H0 E` and let `x ∈ C0`
   be the image of `k` under the projection `E → R` followed by
   `R ⊗ C0 ≅ C0`. By naturality of base change, `d x = 0`, so `x = r • g₀`
   for some `r ∈ R`. Because `inr m · (a, n) = inr (a • m)` in `E`, one gets
   `inr m • k = inr m ⊗ x = inr m ⊗ r • g₀`, which is the image of
   `(r • m) ⊗ g₀ = 0` under `inr ⊗ C0`, hence zero.
2. Let `ψ : G.H0 E ≅ E` and `e = ψ⁻¹(1)`. For `a, b ∈ C`, step 1 gives
   `inr (a - b) • e = 0`, so applying `ψ`, `inr (a - b) = inr (a - b) · 1 = 0`
   in `E`, and taking second components, `a = b`.
