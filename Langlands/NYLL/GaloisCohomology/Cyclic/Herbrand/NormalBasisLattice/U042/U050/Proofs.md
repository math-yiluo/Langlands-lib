# NYLL M144.050: mem_maximalIdealFieldSubmodule_iff

This file proves the exact published proposition
`Langlands.NYLL.CyclicCohomology.mem_maximalIdealFieldSubmodule_iffStatement`
with theorem `Langlands.NYLL.CyclicCohomology.mem_maximalIdealFieldSubmodule_iff`.
The statement and its imported definitions are unchanged.

The carrier of `maximalIdealFieldSubmodule K L` is the set of field
images of elements of the actual maximal ideal in `𝒪[L]`. Unfolding it gives
the existential on the right, so the proof is `Iff.rfl`, exactly the original
implementation. The source simp attribute is retained. Only the published
statement module and its imported definitions are used. The theorem has the
source common universe and field, algebra and valuation-extension instances;
it requires no finite-dimensional, Galois or topological/local-field hypothesis.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 892–899](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L892).
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
