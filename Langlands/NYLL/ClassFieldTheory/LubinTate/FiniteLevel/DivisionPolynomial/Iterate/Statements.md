# Basic targets for standard Lubin–Tate polynomial iterates (M339.010–.013)

These are four proposition-valued definitions (`def … : Prop`), with no
proofs. Each has independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit arguments
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`π : F.valuationSubring` and `n : ℕ`, matching the source theorems.
Write `f = standardLubinTatePolynomial F π` (M339.001, `X ^ q + C π * X`),
`fₙ = standardLubinTatePolynomialIterate F π n` (M339.008, the `n`-fold
compositional iterate of `f` starting from `X`), and
`q = Nat.card F.residueField`. All names have prefix
`Langlands.NYLL.LubinTate`.

| Source unit | Source line | Declaration | Proposition |
| --- | --- | --- | --- |
| M339.010 | 146 | `standardLubinTatePolynomialIterate_succStatement` | `standardLubinTatePolynomialIterate F π (n + 1) = (standardLubinTatePolynomial F π).comp (standardLubinTatePolynomialIterate F π n)` |
| M339.011 | 156 | `standardLubinTatePolynomialIterate_natDegreeStatement` | `(standardLubinTatePolynomialIterate F π n).natDegree = Nat.card F.residueField ^ n` |
| M339.012 | 166 | `standardLubinTatePolynomialIterate_monicStatement` | `(standardLubinTatePolynomialIterate F π n).Monic` |
| M339.013 | 184 | `standardLubinTatePolynomialIterate_eval_zeroStatement` | `(standardLubinTatePolynomialIterate F π n).eval 0 = 0` |

In words:

- M339.010: `fₙ₊₁ = f ∘ fₙ`, i.e. one more composition with `f` on the outside.
- M339.011: `fₙ` has natural degree `q ^ n`.
- M339.012: `fₙ` is monic.
- M339.013: `fₙ(0) = 0` in the valuation subring.

No hypothesis on `π` is added; it need not be a uniformizer. The degree
and monicity claims hold because the residue field of a LocalField
package is finite and nontrivial, so `q ≥ 2`. These statements carry no
such hypothesis: the source derives it from the inherited
`Finite F.residueField` instance. This pair asserts the propositions only.
Their proofs are separate exact-proof obligations for the proof owner
(Worker 298, Task 5888).

The zero-iterate assertion M339.009 has no target here. It holds by direct
definitional reduction of M339.008 (see the `Definitions` pair).

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
The statement types are at these lines:

- M339.010: declaration line 146, type lines 147–150 (proof 151–153).
- M339.011: line 156, type lines 157–159 (proof 160–163).
- M339.012: line 166, type lines 167–168 (proof 169–180).
- M339.013: line 184, type lines 185–186 (proof 187–196).

Source file SHA-256:
`3792ba23d5445d4367d7f28cf536ee4d1419e8675fab3155b500673efcb2b395`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21` (content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (content hash
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications:

- Each source `theorem` becomes a `def … : Prop` named with `Statement`
  appended. The binders (`F`, `π`, `n` explicit; `K`, `Field K` implicit
  from the source `variable`), universes and proposition are unchanged.
- The source proofs are omitted. The source `@[simp]` attribute on M339.013
  is omitted because a proposition definition is not a simp lemma.
- Namespace: source `LubinTate` becomes `Langlands.NYLL.LubinTate`. The source
  `open LocalFieldTheory.DiscreteValuationField` resolves inside it to the
  published `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Imports: two focused imports.
  - The sibling module
    `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`.
    It brings in M339.008, the published M339.001 definition, the shared
    LocalField package and `Mathlib.Algebra.Polynomial.Eval.Defs`
    (`Polynomial.comp`, `Polynomial.eval`).
  - `Mathlib.Algebra.Polynomial.Degree.Defs`, which defines
    `Polynomial.natDegree` and `Polynomial.Monic`.

  The source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries`
  and `Mathlib.Algebra.Polynomial.Monic`; the standard formal-module series is
  not used.
- The docstrings are adapted to name the source unit. The module documentation
  is new, and the unused `open scoped Polynomial PowerSeries` is dropped.
- M339.009 and M339.014 onward are not included.

The Lean header keeps the original copyright, Apache-2.0 notice and
authorship, and adds a modification line. The source file is not one of the
Anthropic-derived files listed in the supplement's
`Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md`. Licensing and attribution
stay in the existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This unit does not change either file.
