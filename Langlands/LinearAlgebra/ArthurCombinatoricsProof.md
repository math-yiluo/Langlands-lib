# Proof of Arthur's combinatorial lemmas

Author: Worker 3657.

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsProof`. It is the
entry module of the proof of the published statement
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (module
`Langlands.LinearAlgebra.ArthurCombinatoricsStatement`; Task 7174):

```lean
theorem Langlands.ArthurCombinatorics.arthurCombinatoricsStatement :
    ArthurCombinatoricsStatement.{u}
```

The statement is the conjunction of six propositions. The task asks that each
be proved as its own named theorem, so that later work can import them one at
a time. The theorem above is the anonymous-constructor tuple of these six
theorems:

| Conjunct | Theorem | Module | Source |
|---|---|---|---|
| `AlternatingSumStatement` | `alternatingSumStatement` | `ArthurCombinatoricsAlternating` | Arthur 1978, Proposition 1.1, p.916 |
| `TauTauHatVanishingStatement` | `tauTauHatVanishingStatement` | `ArthurCombinatoricsSigma` | Arthur 1978, remark after Corollary 6.2, p.940 |
| `SigmaCharacterizationStatement` | `sigmaCharacterizationStatement` | `ArthurCombinatoricsSigma` | Arthur 1978, Lemma 6.1, pp.938–939 |
| `LanglandsCombinatorialLemmaStatement` | `langlandsCombinatorialLemmaStatement` | `ArthurCombinatoricsLanglandsLemma` | Arthur 1978, Lemma 6.3, pp.940–941 |
| `TauTauHatSigmaExpansionStatement` | `tauTauHatSigmaExpansionStatement` | `ArthurCombinatoricsAlternating` | Arthur 2005, (8.2), p.41 |
| `SigmaSupportStatement` | `sigmaSupportStatement` | `ArthurCombinatoricsSigmaSupport` | Arthur 2005, Lemma 8.3, p.42 |

All modules are in `Langlands/LinearAlgebra/`. Each has its own Markdown
with the implemented proof and exact source locators. The geometric input
shared by Lemma 6.1, the remark after Corollary 6.2 and Lemma 8.3 is that
every weight is a nonnegative combination of the simple roots. It is
`cartanBlock_inv_nonneg` in the helper module
`ArthurCombinatoricsCartanInverse`.

Module dependencies:

- `ArthurCombinatoricsAlternating` imports the published statement module.
- `ArthurCombinatoricsCartanInverse` imports the published definitions
  module `ArthurCombinatorics` and Mathlib's
  `LinearAlgebra.RootSystem.Finite.Nondegenerate`.
- `ArthurCombinatoricsSigma` imports the two modules above.
- `ArthurCombinatoricsSigmaSupport` and `ArthurCombinatoricsLanglandsLemma`
  each import `ArthurCombinatoricsSigma`.
- This module imports the last two.

No published file is changed. All hypotheses and the universe `u` of the
statement are kept.

## Sources

- J. Arthur, *A trace formula for reductive groups I: terms associated to
  classes in G(Q)*, Duke Math. J. 45 (1978), 911–952, registered as
  `arthur-1978-trace-formula-reductive-groups-I`. PDF page = printed
  page − 910.
- J. Arthur, *An introduction to the trace formula* (2005), in the volume
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`.
  PDF page = printed page + 12.

## Submission context

The proof task is Task 7174 (`fc99d3a8-d98b-4d1b-933c-db958e05059d`). It replaces
Task 5768 (`4e277fc9-6303-4213-bb44-eaea2babfdc1`), which the operator retired
(message `37d9a1c6be9f5f6186de2d70b51a3234`, 15 November 2026). Worker 3657 wrote
this draft and is coauthor of the submission. Worker 7 checked the draft
against the sources and submits it; the only change from the draft is the
page locator of (8.2) (p.41, PDF page 53). The target statement is the
published one, unchanged.

## Axioms

`lean_check` c476c2ed (lake build of all six modules over Library
`72480b70`, no errors or warnings): `arthurCombinatoricsStatement` depends
only on `propext`, `Classical.choice` and `Quot.sound`.
The recheck `lean_check` ecb7a057 by Worker 7 (lake build of the six
modules as submitted) gives the same result.
