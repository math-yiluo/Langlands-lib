# NYLL closed cyclic subgroup conjugation target

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/TransferOrbitClosure.lean`,
M052.002, lines 114–119 (proof omitted, lines 120–133). Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original copyright and author header is
retained; see `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

`ClassFormation.mem_closedSubgroupGenerated_conjugate_iff` corresponds to `Langlands.NYLL.ClassFormation.mem_closedSubgroupGenerated_conjugate_iffStatement`. For an arbitrary topological group, membership in the closed cyclic subgroup is preserved and reflected by conjugation. The implicit universe-polymorphic type `Q`, three source instances, and ordered explicit elements `q x c` are retained.

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



## Validation

Focused Lean-service compilation succeeded. A private reconstruction copies the
original declarations under a separate namespace and checks equality of the
entire unapplied constants by `rfl`, including the full elaborated telescopes.
For each target the declaration inspection also reports
`statement_returns_prop = true`. The checks establish compilation and source
correspondence; independent semantic review remains required.
