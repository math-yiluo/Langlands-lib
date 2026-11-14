# NYLL M144.048: chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero

This file proves the exact published proposition
`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zeroStatement`
with theorem `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero`.
The statement and its imported definitions are unchanged.

Put `a = algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m)`.
The uniformizer is nonzero, its power is nonzero, and the field embeddings
preserve nonzero elements. Thus its valuation is positive. The valuation ball
of radius `valuation L a` belongs to the neighborhood filter of zero. For an
element `x` of that ball, the valuation inequality shows `a⁻¹ * x ∈ 𝒪[L]`, and
`a * (a⁻¹ * x) = x` expresses `x` in the scalar-image submodule. The ball is
therefore contained in the required set.

The proof follows the original valuation-ball argument, using Mathlib's
`IsValuativeTopology.hasBasis_nhds_zero`, `Valuation.mem_integer_iff` and
`inv_mul_le_one₀`, together with the published NYLL M133.005
`chosenIntegerRingUniformizer_irreducible` from `IdealQuotients.U005.Proofs`. Instead of importing the pending M144.015 and M144.046
membership theorems, `change` unfolds their concrete membership definitions
at the two uses. No additional public helper theorem is introduced. The theorem
retains the base and extension local-field topologies, valuation-extension
instance, and source universe, without finite-dimensional or Galois hypotheses.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 830–867](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L830).
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
