# H⁰ of a two-term complex with fibre dimension at most one is locally an annihilator

`Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one` proves the theorem `P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution`. Its statement is that of `CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one`, which `Langlands.AnthropicFLT.Theorems.Thm_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one` states under its FLT name.

## Statement

Let `R` be a commutative ring and `G` a two-term complex over `R` (the FLT
structure `CoherentBaseChange.TwoTermComplex`: a linear map `d : C0 → C1`
between finite free `R`-modules). For an `R`-algebra `B`, `G.H0 B` is the
kernel of `B ⊗ d`. Let `𝔭` be a prime of `R` with residue field `κ` such that
`G.fibreH0 𝔭 = dim_κ ker (κ ⊗ d) ≤ 1`. Then there are `h ∈ R` with `h ∉ 𝔭`
and an ideal `J` of `R` such that for every `R`-algebra `B` in which `h` is a
unit, `G.H0 B` is isomorphic, as a `B`-module, to the annihilator in `B` of
the extended ideal `J B`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

Choose bases of `C0` and `C1` and let `D` be the matrix of `d`. Let `W` be the
submodule of `R^{ι0}` spanned by the rows of `D` (the image of `Dᵀ`) and
`Q = R^{ι0} / W`, the cokernel of the transpose. For every `B`, `G.H0 B` is
the module of `x ∈ B^{ι0}` with `D x = 0` (`H0Equiv`), and every element of
`W` pairs to zero with such `x` under `⟨v, x⟩ = Σ v_i x_i`.

1. Fibre dimension. Base change preserves cokernels (`baseChangeCokerEquiv`,
   by right exactness of the tensor product), and a matrix and its transpose
   have the same rank over the field `κ`; with rank–nullity this gives
   `dim_κ (κ ⊗ Q) = G.fibreH0 𝔭 ≤ 1` (`finrank_fibre_eq`).
2. A local generator (Nakayama). Since `κ ⊗ Q` has dimension at most one,
   some `q ∈ R^{ι0}` has image spanning it. Then `κ ⊗ (Q / R q) = 0`, so `𝔭`
   is not in the support of the finite module `Q / R q`
   (`Module.mem_support_iff_nontrivial_residueField_tensorProduct`), and some
   `h ∉ 𝔭` annihilates it (`Module.support_eq_zeroLocus`): for every
   `v ∈ R^{ι0}` there is `r_v ∈ R` with `h v - r_v q ∈ W`.
3. Put `J = {r ∈ R : r q ∈ W}` and, for `B` with `h` invertible, let `Φ` send
   `x` with `D x = 0` to `⟨q, x⟩`.
   - Image in the annihilator: for `r ∈ J`, `r ⟨q, x⟩ = ⟨r q, x⟩ = 0`.
   - Injectivity: for the standard basis vector `e_i`,
     `h x_i = h ⟨e_i, x⟩ = r_{e_i} ⟨q, x⟩`, so `Φ x = 0` forces `x = 0`.
   - Surjectivity: for `b` killed by `J B`, put `x_i = h⁻¹ r_{e_i} b`. For each
     row `j`, `Σ_i D_{ji} r_{e_i} ∈ J`, so `D x = 0`; and
     `h - Σ_i q_i r_{e_i} ∈ J`, so `⟨q, x⟩ = h⁻¹ (Σ_i q_i r_{e_i}) b = b`.

Hence `Φ` is an isomorphism of `B`-modules onto the annihilator of `J B`
(`KmatEquivAnn`).
