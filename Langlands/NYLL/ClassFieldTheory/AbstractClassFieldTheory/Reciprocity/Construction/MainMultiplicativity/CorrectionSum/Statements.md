# NYLL correction-sum action-difference target

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/CorrectionSum.lean`,
M056.004, lines 87–95 (proof omitted, lines 96–102). Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original copyright and author header is
retained; see `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

`ClassFormation.frobeniusMultiplicativity_actionDifference_eq_correctionSum` corresponds to `Langlands.NYLL.ClassFormation.frobeniusMultiplicativity_actionDifference_eq_correctionSumStatement`. It states the original three-term action-difference identity as the sum over the actual three correction coefficients and actions, retaining the left-action order `τ₄ * τ₁` and the complete universe-zero representation telescope.

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
