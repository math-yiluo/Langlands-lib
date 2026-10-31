# Global sections of a locally trivial module on a proper flat scheme are computed by a two-term complex universally

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange` proves the theorem `AlgebraicGeometry.Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange`.

## Statement

Let `R` be a noetherian commutative ring in universe `u`, `f : X ⟶ Spec R` a
proper flat morphism and `M` a locally trivial sheaf of modules on `X`
(every point has an open neighbourhood on which the pullback of `M` is
isomorphic to the structure sheaf). For an `R`-algebra `A`, write `M_A` for
the pullback of `M` to `X_A = X ×_{Spec R} Spec A`; global sections are
modules through `f`, respectively the second projection. Then there is a
two-term complex `G` (the FLT structure `CoherentBaseChange.TwoTermComplex`:
a linear map `d : C0 → C1` of finite free `R`-modules) together with

- an `R`-linear isomorphism `ε₀ : Γ(M) ≅ ker d`, and
- for every `R`-algebra `A`, an `A`-linear isomorphism
  `ε_A : Γ(M_A) ≅ ker (A ⊗ d)` (`G.H0 A`),

compatible with base change: for `m ∈ Γ(M)`, `ε_A` sends the pullback of `m`
(its image under the unit of the pullback–pushforward adjunction) to the
image of `1 ⊗ ε₀(m)` under the natural map `A ⊗ ker d → ker (A ⊗ d)`
(`G.kerBaseChangeHom A`).

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange`, which has the same statement. The Markdown of that module outlines the argument.
