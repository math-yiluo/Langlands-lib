# NYLL M144.028: the normal-basis next-step product bound

This file proves exactly
`Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succStatement`
under its unchanged parameters. The result concerns the actual normal-basis
integer lattice of a finite-dimensional Galois extension `L/K`, and the powers
of the chosen uniformizer of the nonarchimedean local base field `K`. All fields
remain in the original arbitrary universe.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 528–539](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L528-L539).
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
Worker 339 extracted the proof on 14 November 2026, added the `Langlands.NYLL`
namespace prefix, narrowed imports and used the unchanged named Library target.
Worker 187 contributed the direct full-span argument. The source's normal-basis
finite-generation fact (M144.008, lines 120–123) and full-span fact (M144.006,
lines 80–87, using M144.001, lines 30–45, and the basis membership argument
of M144.004, lines 67–70) are supplied as local proof facts, without publishing
another copy under their adapted sibling names.

## Implemented proof and dependencies

The proof first unfolds the chosen integer lattice as the integer-ring span
of the normal-basis Galois orbit. The orbit is finite, and
`Submodule.fg_span (Set.finite_range _)` proves finite generation.
For full span over `K`, compare with `(IsGalois.normalBasis K L).span_eq`.
Each basis vector is a Galois conjugate of the chosen normal-basis generator
by `IsGalois.normalBasis_apply`, so it belongs to the integer lattice by
`Submodule.subset_span`. Then `Submodule.span_mono` proves that the field span
of the integer lattice contains the full normal-basis span.

Apply
`exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top`
(M144.026) to this lattice and the two local facts. Its conclusion is definitionally
the target proposition: there is a natural-number threshold such that products
of two elements at every deeper level lie in the next level.

The theorem is imported from `U015.U026.Proofs`; its proof uses M144.023 and,
transitively, M144.021. The local normal-basis facts use the actual Mathlib basis
and Galois group, with no additional assumption package. This result proves
only the stated product estimate for the chosen lattice.
