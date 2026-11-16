# NYLL M144.052: exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg

This file proves the exact published proposition
`Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fgStatement`
with theorem `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg`.
The statement and its imported definitions are unchanged.

Choose a finite set `S` spanning `N`. For each field element, M144.043
supplies an exponent making its uniformizer multiple integral. Take the supremum
of these exponents on the finite generating set. Increasing an exponent preserves
integrality because the extra factor is the image of a base integer-ring element.
Span induction, using the integer ring's closure under addition and base scalar
multiplication, extends the common bound to every element of `N`. An element of
the scalar-image submodule is then integral by its defining witness.

The proof follows source lines 920–969. It imports M144.043 in
`U042.U043.Proofs`; the source's last use of M144.015 is replaced by directly
unpacking the submodule-map membership witness. Integer-ring membership is
likewise reduced definitionally. No additional public helper is introduced.
The theorem retains the source base and extension nonarchimedean local-field
structures and compatible valuations in the common universe, and omits finite
dimensionality and Galois assumptions.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 914–969](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L914).
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
