# The decomposition-group residue action (M243.023–.024)

These data define, in
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
the canonical monoid homomorphism from the decomposition group to the
stabilizer of the chosen valuation ring's maximal ideal, then its action
on the selected residue field as automorphisms over the fixed-subring
residue quotient.

| Row | Source lines | Declaration |
| --- | --- | --- |
| M243.023 | 274–285, declaration 276 | `decompositionGroupToMaximalIdealStabilizer` |
| M243.024 | 287–298, declaration 288 | `decompositionGroupResidueAction` |

Source: Naganori Yamaguchi's NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`.
Both are Type-valued `def`s. They retain the source bodies, proof fields,
docstrings, universes, and section variables. Their actual telescopes are
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
(A : ValuationSubring L)`, without `[IsGalois K L]`. The first inserts an
element of the decomposition group into the stabilizer using M243.022;
its monoid laws are `rfl`. The second composes that homomorphism with
Mathlib's `Ideal.Quotient.stabilizerHom`, using the source invariant-ring,
commuting-action and lies-over instances and M243.021's quotient algebra.
It does not require Galois or finite extension hypotheses.

Modifications: extract the two data rows, prefix the namespace, narrow
imports, and replace module prose with this scope. The source copyright
and author header is preserved with a modification note. The imports are `ResidueFields` (M243.020/.021), `IsInvariantProof`
(M243.014) and `StabilizerEqTopProof` (M243.022). The lies-over instance
M243.019 is imported through `ResidueFields`. Mathlib supplies M243.013's
commuting-action instance. The source action is reused by Lean name in
the later residue-action statements; no surjectivity is proved here.

Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Reuse Apache-2.0 LICENSE and NOTICE in `licenses/NYLL/`.
