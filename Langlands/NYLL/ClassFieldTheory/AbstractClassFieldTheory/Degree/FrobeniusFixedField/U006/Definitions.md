# Natural profinite power map (M014.006)

Worker 193 adapts Naganori Yamaguchi’s `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean>),
lines 92–102 (including its docstring). The full original file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Source correspondence

| Original declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.zHatPowNat` | `Langlands.NYLL.ClassFormation.zHatPowNat` |

The sole parameter is explicit `(n : ℕ)`, with result
`ZHatMul →ₜ* ZHatMul`; there are no ambient group parameters.
`ZHatMul` is the published `Type 0` multiplicative presentation of
the source’s actual closure model `ZHat`. Multiplication in this
presentation is addition in `ZHat`. Evaluation is exactly
`Multiplicative.ofAdd (zHatMulNat n z.toAdd)`, including `n = 0`.
The source’s proofs of one preservation, multiplication preservation
and continuity are retained (`Multiplicative.ext`, simplification of
`zHatMulNat`, `nsmul_add` and `map_continuous`).

| Source dependency | Published declaration reused |
| --- | --- |
| `ClassFormation.ZHatMul` (M010.001) | `Langlands.NYLL.ClassFormation.ZHatMul` |
| `ClassFormation.ZHat` (M008.008) | `Langlands.NYLL.ClassFormation.ZHat` |
| `ClassFormation.zHatMulNat` (M009.002) | `Langlands.NYLL.ClassFormation.zHatMulNat` |

## Modifications and reuse

The source namespace `ClassFormation` is prefixed with `Langlands.NYLL`.
The source `noncomputable section` is retained. Extraction omits the unused
`CyclicCohomology` namespace opening, the unused ambient group section
variables and all other source declarations. No construction field, proof
body, parameter order or binder kind is changed. The three broad source
imports (`Degree.FrobeniusLift`, `ProfiniteIntegers.TopologicalGeneration`
and `Topology.TotallyDisconnectedQuotients`) are replaced by:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`
- `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions`

The published dependencies and Mathlib constructions are reused by Lean name;
this unit introduces no instances. Exact-name Library search found no
previously published declaration for this source unit. The focused Mathlib
continuous-homomorphism, quotient and subgroup source search found no
bundled definition replacing this full source construction and telescope.

This is a data-definition candidate, including its intrinsic structure
proofs. It publishes no separate theorem target and claims no Frobenius
fixed-field, host class-formation, cohomology or reciprocity theorem.

## License

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already published in the Library and unchanged.
All modifications above are by Worker 193.
