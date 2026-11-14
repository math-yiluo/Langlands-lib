# NYLL M144.023: a common exponent for lattice products

The theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top`
proves exactly its published `Statement` proposition. Over arbitrary fields
`K L : Type u` with `L` a `K`-algebra and `K` a valued nonarchimedean local
field, finite generation of integer-ring submodules `N` and `P` and full
field span of `M` give a natural exponent sending every product `x*y`,
`x ∈ N`, `y ∈ P`, into `M` after multiplication by that uniformizer power.
No finite-dimensionality or Galois hypothesis is assumed.

## Implemented proof and dependencies

Choose finite spanning sets of `N` and `P`. For each pair of generators,
M144.021 supplies an exponent clearing the denominator of their product.
Take the supremum over the finite Cartesian product. The source's local
`hpow_mono` argument raises each pair's exponent to this common bound by
integral scalar multiplication. First span induction in the right variable,
and then span induction in the left variable, extend the bound to all
products. Zero, additivity and integral scalar closure handle the induction
steps; commutative ring identities put products in the required form.

The direct imports are the unchanged `U015.Statements` and preceding
`U015.U021.Proofs`. M144.021 uses the published scalar denominator-clearing
result from `IdealQuotients.U020.Proofs`. The proof retains the source's local
monotonicity argument and introduces no extra public prerequisite theorem.
The finite Cartesian product and its supremum also cover empty spanning sets.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean),
M144.023, lines 358–433 (unit ends at 434).
The pinned source SHA-256 is
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

Worker 187 extracted this proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix and exact statement application, and
replaced the source imports with the displayed imports. The implemented
finite bound and two span inductions follow the source. The original
copyright and author header is preserved; Apache-2.0
`licenses/NYLL/LICENSE` and `NOTICE` remain unchanged. This support result
discharges no host class-formation, cup, transfer, Tate or reciprocity target.
