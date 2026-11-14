# NYLL M144.021: denominator clearing in a spanning lattice

The theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top`
proves exactly the published proposition with the same name plus `Statement`.
For arbitrary fields `K L : Type u`, a `K`-algebra structure on `L`, and the
valuation, topology and nonarchimedean local-field structure on `K`, every
`x : L` enters an integer-ring submodule `M` after multiplication by some
natural power of the chosen base uniformizer, provided `M` spans `L` over `K`.
No finite-dimensionality or Galois hypothesis is required.

## Implemented proof and dependencies

The full-span hypothesis places `x` in the field span of `M`. Span induction
proves denominator clearing for each element: a generator or zero needs exponent
zero; sums use the maximum of the two exponents. The private helper
`uniformizerPow_mul_mem_of_le` raises an exponent by multiplying by the
remaining integral power and applying submodule scalar closure. For a field
scalar `c`, the published theorem
`Langlands.NYLL.LocalFieldTheory.exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing`
provides a power making `c` integral. Multiplying by that integral scalar and
combining exponents proves the scalar step. Algebra-map identities and ring
normalization identify the resulting product.

The direct imports are the unchanged `U015.Statements` module and published
`IdealQuotients.U020.Proofs`. All lattices, uniformizers and scalar maps are the
actual published definitions. The private exponent helper is a local adaptation
of M144.017 because its sibling proof was unpublished at implementation time;
it adds no public prerequisite theorem or additional assumption.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean),
M144.021, lines 244–290 (unit ends at 296), with the private helper from
M144.017, lines 196–205 (unit ends at 210).
The pinned source SHA-256 is
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

Worker 187 extracted these proofs on 14 November 2026, added the
`Langlands.NYLL` namespace prefix and exact statement application, made the
monotonicity helper private under a different name, and replaced the source
module imports with the displayed published imports. The implemented span
induction follows the original proof. The original copyright and author
header is preserved, with Apache-2.0 `licenses/NYLL/LICENSE` and `NOTICE`
unchanged. This support theorem discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
