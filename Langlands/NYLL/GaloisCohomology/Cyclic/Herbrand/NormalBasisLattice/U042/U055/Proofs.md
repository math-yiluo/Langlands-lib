# NYLL M144.055: chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule

This file proves the exact published proposition
`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmoduleStatement`
with theorem `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule`.
The statement and its imported definitions are unchanged.

Represent an element of the `(b + 1)`-power submodule by a scalar
multiple of `y ∈ N`. The hypothesis makes `π_K^b * y` integral, so it defines
`z : 𝒪[L]`. The image `πL` of the base uniformizer belongs to the maximal
ideal; hence `πL * z` does as well. Its image in `L` equals the original element
by `pow_add` and the ring-map laws. This is the source factorization proof.
Scalar-image, integral and maximal-ideal membership are reduced directly,
replacing the source uses of M144.015, M144.046 and M144.050.

The private helper `baseUniformizer_image_in_maximalIdeal` implements the source
M144.042 proof (lines 687–697) under a non-conflicting private name: the base
uniformizer belongs to the principal ideal it generates, the published
`chosenIntegerRingUniformizer_maximalIdeal_eq` (M133.006) identifies that ideal
with the base maximal ideal, and Mathlib's
`Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff` transports membership.
The original M144.042 adapted public name remains with its sibling task.

Actual dependencies are the published U042 statement/data imports, M133.006 in
`IdealQuotients.U006.Proofs`, and Mathlib's valuation-extension and ideal laws.
The theorem retains the source base local-field and valuation-extension
instances and common universe, without finite-dimensional or Galois assumptions.
No extension topology is needed.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 998–1034](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L998).
The retained file is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum is recorded in `notes/errata/`.

Worker 641 extracted this proof on 14 November 2026, prefixed the namespace
with `Langlands.NYLL`, replaced the displayed conclusion by its exact
published Prop definition, and replaced source-wide imports with the imports
shown in Lean. Any further proof adaptations are described above.
The original copyright and author header is retained; the Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain Apache-2.0 attribution.
This support proof discharges no host class-formation, cup, transfer, Tate,
or reciprocity statement.
