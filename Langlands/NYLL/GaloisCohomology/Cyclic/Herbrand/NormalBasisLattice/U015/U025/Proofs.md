# NYLL M144.025: multiplication in deep uniformizer lattices

The theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top`
proves exactly its published `Statement` proposition. For fields
`K L : Type u`, a `K`-algebra structure on `L`, and a valued nonarchimedean
local field structure on `K`, let `M` be a finitely generated
`𝒪[K]`-submodule whose `K`-span is all of `L`. There is a natural bound
`c` such that for every `n ≥ c`, the submodule `π_K^n M` is closed under
products. The power uses the actual chosen integer-ring uniformizer.
No finite-dimensionality or Galois hypothesis is assumed.

## Implemented proof and dependencies

Apply M144.023 with both factor submodules equal to `M`. It gives `c`
such that `π_K^c (x₀*y₀)` belongs to `M` for every `x₀,y₀ ∈ M`.
For `n ≥ c`, integral scalar multiplication raises this exponent to `n`.
Write elements of `π_K^n M` as `π_K^n x₀` and `π_K^n y₀`, using the
definition of the scalar-image submodule. Their product is the image
under multiplication by `π_K^n` of `π_K^n (x₀*y₀) ∈ M`. Commutativity
and associativity verify the witness equation.

The direct imports are the unchanged `U015.Statements` and
`U015.U023.Proofs`. The latter uses M144.021 and its published scalar
denominator-clearing dependency from `IdealQuotients.U020.Proofs`.
The private helper `latticeProduct_pow_mul_mem_of_le` implements the
source's M144.017 exponent argument: write `n = c+d` and use closure
under the integral scalar `π_K^d`. The source's M144.015 membership
equivalence is expanded definitionally with `change`, using the actual
submodule image. These local adaptations are permitted by the task
while the sibling proofs await publication; they introduce no public
declaration under the sibling targets' names.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean),
M144.025, lines 453–476 (source unit 453–483).
The exponent helper follows M144.017, lines 196–207.
The source SHA-256 is
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

Worker 187 extracted the proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix and exact statement application,
replaced source imports with the displayed imports, and made the local
membership and exponent adaptations described above. The original
copyright and author header is preserved; Apache-2.0
`licenses/NYLL/LICENSE` and `NOTICE` remain unchanged. This support result
discharges no host class-formation, cup, transfer, Tate or reciprocity target.
