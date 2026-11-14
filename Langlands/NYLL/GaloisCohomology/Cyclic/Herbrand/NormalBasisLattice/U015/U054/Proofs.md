# NYLL M144.054: chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le

This file proves the exact published proposition
`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_leStatement`
with theorem `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le`.
The statement and its imported definitions are unchanged.

Write an element of the `(a + n)`-power scalar-image submodule as
`π_K^(a+n) * y`, with `y ∈ N`. The assumed containment puts `π_K^a * y` in
`M`. This element witnesses membership in the `n`-power scalar-image of `M`,
and `pow_add`, `map_mul`, associativity and commutativity verify its image.
This is the source proof with scalar-image membership reduced directly in
`rcases` and `refine`, replacing its uses of pending M144.015.

The published U015 statement and its imported concrete data are the only NYLL
dependencies. The proof requires the base local-field structure for its chosen
uniformizer, but no finite-dimensional or Galois structure and no valuation on
`L`. The source common universe and scalar action are unchanged.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 981–997](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L981).
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
