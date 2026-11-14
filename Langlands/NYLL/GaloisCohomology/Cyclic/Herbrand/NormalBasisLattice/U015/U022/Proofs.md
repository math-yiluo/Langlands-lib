# NYLL M144.022: a common exponent for finite generators

The theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top`
proves exactly its published `Statement` proposition. For arbitrary fields
`K L : Type u`, a `K`-algebra `L`, and a valued nonarchimedean local field `K`,
if `N` is a finitely generated integer-ring submodule and `M` spans `L` over
`K`, some natural exponent `n` satisfies `π_K^n N ≤ M`. There is no
finite-dimensionality or Galois hypothesis.

## Implemented proof and dependencies

Choose a finite spanning set of `N`. M144.021 gives a denominator-clearing
exponent for every generator; take their finite supremum. The local
`hpow_mono` argument raises each generator's exponent to that supremum by
submodule scalar closure. Span induction then proves that multiplying every
element of `N` by the common power lands in `M`: sums use distributivity and
integral scalar multiples use commutativity and scalar closure. Finally,
unfolding the actual image-submodule membership expresses an element of
`π_K^n N` as that scalar times an element of `N`.

The direct imports are the unchanged `U015.Statements` and the preceding
`U015.U021.Proofs`. M144.021 in turn uses published scalar denominator
clearing from `IdealQuotients.U020.Proofs`. Membership in the scalar-image
submodule is definitionally the existential witness condition, so the
unpublished sibling M144.015 is expanded locally; no additional public
prerequisite theorem is introduced. The local monotonicity proof is the same
one included in the original M144.022 proof.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean),
M144.022, lines 297–351 (unit ends at 357).
The pinned source SHA-256 is
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

Worker 187 extracted this proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix and exact statement application, replaced
the original imports by the displayed imports, and replaced the reference
to M144.015 by a definitional `change` exposing the same witness condition.
The finite supremum and span-induction argument follows the source. The
original copyright and author header is preserved; Apache-2.0
`licenses/NYLL/LICENSE` and `NOTICE` remain unchanged. This support theorem
discharges no host class-formation, cup, transfer, Tate or reciprocity target.
