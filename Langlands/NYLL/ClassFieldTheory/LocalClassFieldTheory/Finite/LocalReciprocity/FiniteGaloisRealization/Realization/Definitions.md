# Finite Galois field ranges and fixing subgroups

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M090.001 | `finiteGaloisFieldRangeOfEmbedding` (37–43) | `finiteGaloisFieldRangeOfEmbedding` |
| M090.002 | `finiteGaloisFieldRangeEquivOfEmbedding` (45–49) | `finiteGaloisFieldRangeEquivOfEmbedding` |
| M090.003 | `finiteGaloisFieldRangeOfEmbedding_isGalois` (51–55) | `finiteGaloisFieldRangeOfEmbedding_isGalois` |
| M090.004 | `finiteGaloisFieldRangeOfEmbedding_finiteDimensional` (57–61) | `finiteGaloisFieldRangeOfEmbedding_finiteDimensional` |
| M090.005 | `finiteGaloisClosedFixingSubgroupOfEmbedding` (63–69) | `finiteGaloisClosedFixingSubgroupOfEmbedding` |
| M090.011 | `finiteGaloisFieldRange` (169–172) | `finiteGaloisFieldRange` |
| M090.013 | `finiteGaloisFieldRange_isGalois` (180–184) | `finiteGaloisFieldRange_isGalois` |
| M090.014 | `finiteGaloisFieldRange_finiteDimensional` (186–190) | `finiteGaloisFieldRange_finiteDimensional` |
| M090.015 | `finiteGaloisClosedFixingSubgroup` (192–197) | `finiteGaloisClosedFixingSubgroup` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace and reuse the published separable-closure embedding and closed-fixing-subgroup modules through focused imports. Omit unused namespace openings. All nine original declaration bodies, universes, binder kinds and instance scopes are retained. The common context is the source lines 32–33, with K and L both Type 0. Lean retains only the section hypotheses actually used by each body, as in the source: the explicit range and its equivalence need neither finite-dimensionality nor Galoisness. The chosen range uses the published separable embedding, whose separability instance is inferred from the source Galois hypothesis.

These are the actual images in the chosen separable closure, the algebra equivalence supplied by the embedding, the source Galois and finite-dimensional instances, and the actual closed fixing subgroups. No alternative abstract fields or assumed equivalences are introduced.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
