# NYLL M144.026: products land in the next lattice step

This file proves exactly
`Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_topStatement`
with the required source-adapted theorem name. It preserves the arbitrary universe,
base and extension fields, algebra structure, valuation and local-field topology
on the base, and the finite-generation and full-field-span hypotheses. It requires
neither finite dimensionality nor a Galois extension.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 484–510](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L484-L510).
The retained source file is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It belongs to registered source `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`),
also covered by `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`).
No applicable NYLL erratum is recorded under `notes/errata/`.

The original copyright and author header is retained verbatim. Apache-2.0
attribution remains in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 339 extracted this proof on 14 November 2026, added the `Langlands.NYLL`
namespace prefix, narrowed imports and stated its type through the unchanged
Library proposition target. The source argument is retained, with the source
M144.015 membership equivalence (lines 178–183) and M144.017 monotonicity
argument (lines 196–207) implemented as local proof facts. No additional public
copy of those sibling theorem names is introduced.

## Implemented proof

Apply M144.023 with all three submodules equal to `M`. It supplies an exponent
`c` such that multiplying any product of two members of `M` by the `c`th power
of the chosen base uniformizer puts it in `M`. Use `c + 1` as the bound.
For `n ≥ c + 1`, write `n = (c + 1) + d`, and express the two given elements
as `π^n x₀` and `π^n y₀` with `x₀, y₀ ∈ M`, using the definitional description
of the scalar-image submodule.

The local monotonicity fact follows by multiplying an existing member of `M`
by the remaining power of the base integer-ring uniformizer; it uses only
`M.smul_mem`, `Algebra.smul_def` and power/multiplication identities. It puts
`π^(c+d) (x₀ y₀)` in `M`. This is the witness for membership of the product in
`π^(n+1) M`: the exponents satisfy `(n + 1) + (c + d) = 2*n`.
After expanding powers and their algebra maps, `ring` proves the witness equality.

The non-Mathlib theorem dependency is
`exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top`, imported
from `U015.U023.Proofs`; that proof imports M144.021. Membership is definitional
for the actual `chosenBaseUniformizerPowSubmodule` construction. This result
proves the stated lattice product estimate only.
