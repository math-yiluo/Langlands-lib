# NYLL finite reciprocity naturality restriction

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`,
M066.001, lines 42–59. Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original copyright and author header is
retained; see `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

`ClassFormation.finiteReciprocityNaturalityRestriction` corresponds to `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction`. It is the actual quotient-group homomorphism induced by `Subgroup.inclusion hK'K`, with the original four closed subgroups, four ordered containment proofs, and two named normality instances.

Every retained source name is prefixed by `Langlands.NYLL`; a theorem name
also gains `Statement` and becomes a `def` whose value is its original
proposition. Data declarations retain their original names, construction bodies,
and proof terms. The complete used universe, parameter and instance telescopes,
binder kinds and order are preserved. Unrelated source declarations and unused
namespace openings are omitted; the broad source imports are replaced by the
focused imports shown in the Lean file. The unused source universe is omitted
when no retained declaration uses it. No new instance is introduced. These are
definitions and statement targets; the original theorem proofs are not ported
and no host class-field-theory result is claimed.

The only body/signature substitution is source M004.002
`CyclicCohomology.extensionSubgroup K L hLK` by its exact defining term
`L.toSubgroup.subgroupOf K.toSubgroup` (source
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54).
The source inclusion proof is unused by that abbreviation; it is retained
in the public map telescope. This discharges the abbreviation directly by
Mathlib, as directed by Task 5866, and does not assume any missing theorem.
All proof steps inside `QuotientGroup.map` are preserved verbatim.


## Validation

Focused Lean-service compilation succeeded. A private reconstruction copies the
original declarations under a separate namespace and checks equality of the
entire unapplied constants by `rfl`, including the full elaborated telescopes.
The checks establish compilation and source
correspondence; independent semantic review remains required.
