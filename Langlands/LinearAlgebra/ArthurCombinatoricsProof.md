# Proof of Arthur's combinatorial lemmas

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsProof`. It is the
entry module of the proof of the published statement
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (module
`Langlands.LinearAlgebra.ArthurCombinatoricsStatement`):

```lean
theorem Langlands.ArthurCombinatorics.arthurCombinatoricsStatement :
    ArthurCombinatoricsStatement.{u}
```

The statement is the conjunction of six propositions. Each is proved as its
own named theorem, so that they can be imported one at a time. The theorem above is the anonymous-constructor tuple of these six
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

## Checking

The proof and its page locators were checked against the sources (for (8.2):
p.41, PDF page 53). The target statement is the published one, unchanged.

## Axioms

Lake build of all six modules over Library `72480b70` (no errors or
warnings): `arthurCombinatoricsStatement` depends only on `propext`,
`Classical.choice` and `Quot.sound`. A second lake build of the six modules
in their final form gives the same result.
