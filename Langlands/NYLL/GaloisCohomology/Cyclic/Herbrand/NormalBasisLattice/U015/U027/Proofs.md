# NYLL M144.027: multiplication in deep normal-basis lattices

The theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self`
proves exactly its published `Statement` proposition. For a finite-dimensional
Galois extension of fields `K L : Type u`, with `K` a valued
nonarchimedean local field, all sufficiently deep chosen uniformizer
multiples of `chosenNormalBasisIntegerLattice K L` are closed under
products. The lattice and uniformizer are the actual Library choices;
the statement makes no independence-of-choice claim.

## Implemented proof and dependencies

Apply M144.025 to the chosen normal-basis integer lattice. Two private
prerequisites discharge its hypotheses. Finite generation follows because
the lattice is the integer-ring span of the finite Galois orbit.
For full field span, Mathlib's `IsGalois.normalBasis K L` spans `L` over
`K`. Every basis vector equals the corresponding Galois conjugate of its
vector at the identity, by `IsGalois.normalBasis_apply`, and therefore
lies in the integer-ring span defining the lattice. Monotonicity of
`K`-span gives the inclusion from the top submodule; the reverse
inclusion is automatic.

The direct imports are the unchanged `U015.Statements` and
`U015.U025.Proofs`. M144.025 uses M144.023, M144.021, and the published
scalar denominator-clearing theorem in `IdealQuotients.U020.Proofs`.
The private helpers `normalBasisProduct_lattice_fg` and
`normalBasisProduct_lattice_field_span` supply only the unpublished sibling
prerequisites needed here. They introduce no public declaration under
M144.006 or M144.008's reserved theorem names.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean),
M144.027, lines 514–525 (source unit 514–527).
The local finite-generation proof is M144.008, lines 120–123.
The full-span argument adapts M144.006, lines 80–87, using directly the
normal-basis membership step of M144.004, lines 67–70, and Mathlib's
basis span theorem instead of the intermediate conjugate-range equality
in M144.001, lines 30–45.
The source SHA-256 is
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
It is registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

Worker 187 extracted this proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix and exact statement application,
replaced source imports with the displayed imports, and supplied the
private prerequisite adaptations described above, as permitted by the
task while sibling proofs await publication. The original copyright
and author header is preserved; Apache-2.0 `licenses/NYLL/LICENSE` and
`NOTICE` remain unchanged. This support result discharges no host
class-formation, cup, transfer, Tate or reciprocity target.
