# A bounded flat complex with finite cohomology has a two-term free model for H⁰ universally

`Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex` proves the theorem `P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.solution`. Its statement is that of `Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`, which `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex` states under its FLT name.

## Statement

Let `R` be a noetherian commutative ring and
`C^0 → C^1 → C^2 → …` a cochain complex of flat `R`-modules (`d_{i+1} ∘ d_i = 0`)
that vanishes above some degree `n` (each `C^i` with `i > n` is a
subsingleton). Suppose `ker d_0` is a finite `R`-module and every cohomology
module `ker d_{i+1} / im d_i` is finite. Then there are a two-term complex `G`
(the FLT structure `CoherentBaseChange.TwoTermComplex`: a linear map
`d : C0 → C1` of finite free `R`-modules) and linear maps `ι0 : C0 → C^0`,
`ι1 : C1 → C^1` with `d_0 ∘ ι0 = ι1 ∘ d`, such that for every `R`-algebra `A`
the induced map `ker (A ⊗ d) → ker (A ⊗ d_0)`
(`TwoChartCech.kerMapBaseChange`) is bijective.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The argument is the usual replacement of a bounded flat complex with finite
cohomology by a complex of finite projective modules (the FLT namespace
`P2mMumfordKerModel` refers to Mumford's version), carried out for `H⁰`
only.

1. Truncations. A truncation at degree `p` (`Trunc d p`) is a flat module `K`
   with maps `e : C^p → K` and `ι : K → C^{p+1}` such that `ι ∘ e = d_p`,
   `ker (A ⊗ e) = ker (A ⊗ d_p)` for every `A` (in particular for `A = R`), and
   `K / im e` is finite. For `p ≥ n`, `K = C^{p+1} = 0` and `e = d_p` work.
2. Descending step. Given a truncation `e : C^{p+1} → K` at `p + 1`, choose a
   map `g : R^m → K` such that `(e, g) : C^{p+1} × R^m → K` is surjective
   (lift generators of the finite module `K / im e`; `R^m` is projective). Its
   kernel `K'` is flat, as the kernel of a surjection of flat modules
   (`flat_prod`, `flat_ker_of_surjective`). Since `d_p` lands in
   `ker d_{p+1} = ker e`, `x ↦ (d_p x, 0)` defines `e' : C^p → K'`, and `ι'` is
   the first projection. Because `K` is flat, `A ⊗ K'` is still the kernel of
   `A ⊗ (e, g)` (`subtype_baseChange_injective`), so `ker (A ⊗ e') = ker (A ⊗ d_p)`.
   Finally `K' / im e'` maps to `R^m` by the second projection with kernel a
   quotient of `ker e / im d_p = ker d_{p+1} / im d_p`, which is finite; as
   `R` is noetherian, `K' / im e'` is finite (`finite_coker_e'`). Induction
   gives a truncation at degree `0` (`exists_trunc_zero`).
3. The model. Apply the construction of step 2 once more to the truncation
   `e : C^0 → K` at degree `0`: `K' = ker ((e, g) : C^0 × R^m → K)` with the
   two projections `φ₀ : K' → C^0` and `δ : K' → R^m`, so that
   `e ∘ φ₀ = -g ∘ δ`. Now `K'` is finitely generated, because `ker e = ker d_0`
   is finite and `R^m` is noetherian (`fg_Kx`). A finite flat module over a
   noetherian ring is finitely presented and hence projective, so there are a
   surjection `s : R^n → K'` and a section `i : K' → R^n` with `s ∘ i = id`.
   Put `C0 = R^n`, `C1 = R^m × R^n`, `d = (δ ∘ s, id - i ∘ s)`,
   `ι0 = φ₀ ∘ s` and `ι1 = ι ∘ (-g) ∘ fst`; the square commutes by
   `e ∘ φ₀ = -g ∘ δ` and `ι ∘ e = d_0`.
4. Bijectivity after base change to `A`. An element of `A ⊗ K'` is zero if its
   images under `φ₀` and `δ` are zero (`eq_zero_of_δ_φ₀`). If `x ∈ ker (A ⊗ d)`
   maps to zero, then `s x` has zero images under `φ₀` and `δ`, so `s x = 0`,
   and the second component of `d x = 0` gives `x = i s x = 0`. Conversely, for
   `y ∈ ker (A ⊗ d_0) = ker (A ⊗ e)`, exactness of the base-changed kernel
   sequence gives `w ∈ A ⊗ K'` with `δ w = 0` and `φ₀ w = y`
   (`exists_of_baseChange_eq_zero`); then `i w ∈ ker (A ⊗ d)` and it maps to
   `φ₀ (s (i w)) = φ₀ w = y`.
