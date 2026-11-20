# Proof: the irreducibility criterion for principal series of `GL_n(ℂ)`, "if" direction

Lean module: `Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionProof`.
Worker 1008 wrote it for Task 7102 (`d350e594-f9e8-498f-8c26-2d03b2e7f9a9`).

## Statement proved

`Langlands.Archimedean.complexStandardIrreducibleCriterion :
ComplexStandardIrreducibleCriterionStatement` (Library statement in module
`Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit`). The theorem has no
hypotheses: it is exactly the statement.

For every `n : ℕ` and every list `ds : List ComplexCharacterData` with `ds.length = n`,
`IsComplexLanglandsOrdered ds` and `IsComplexUnlinked ds`, it gives
`IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)`. So the space of
`U(n)`-finite functions of `complexStandardModule n ds` is nonzero, and its only subspaces stable
under both `complexStandardRep n ds` and `complexStandardLie n ds` are `⊥` and `⊤`.

This is the "if" direction of the irreducibility criterion for principal series of `GL_n(ℂ)`
(Tadić 2009, §3: linkage on p. 11, Lemmas 3.2 and 3.3 on pp. 12–13; going back to Želobenko).
The statement's Markdown, `ComplexLargeStandardIrreducibleSplit.md`, explains how the Library's
`ComplexCharacterData` and `IsComplexLinked` match Tadić's `γ(x, y)` and his linkage relation.

## Proof

The proof is one term. It composes five proved Library theorems and adds no new mathematics:

```lean
theorem complexStandardIrreducibleCriterion : ComplexStandardIrreducibleCriterionStatement :=
  complexStandardIrreducibleCriterionReduction
    (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible)
    (complexReverseIntertwinerKernelReduction complexTemperedStandardIrreducible)
```

1. **Unlinked principal series of `GL_2(ℂ)` are irreducible.** `complexGLTwoUnlinkedIrreducible`
   (module `ComplexGLTwoUnlinkedIrreducibleProof`) proves `ComplexGLTwoUnlinkedIrreducibleStatement`.
   For two unlinked complex characters `d`, `e`, the `(𝔤𝔩_2(ℂ), U(2))`-module of the principal
   series of `[d, e]` is irreducible (Tadić 2009, p. 11).
2. **Unlinked swaps.** `complexStandardUnlinkedSwapReduction` (module
   `ComplexStandardUnlinkedSwapReduction`) turns step 1 into `ComplexStandardUnlinkedSwapStatement`.
   If `pre ++ d :: e :: post` has length `n` and `d`, `e` are not linked, a bijective
   `(𝔤, K)`-intertwiner goes from the `U(n)`-finite functions of the standard module of
   `pre ++ e :: d :: post` onto those of `pre ++ d :: e :: post`.
3. **Tempered irreducibility.** `complexTemperedStandardIrreducible` (module
   `ComplexTemperedStandardIrreducibleProof`) proves `ComplexTemperedStandardIrreducibleStatement`.
   Standard modules whose characters all have exponents with the same real part are irreducible.
4. **Intertwiners to the reversed module.** `complexReverseIntertwinerKernelReduction` (module
   `ComplexReverseIntertwinerTied`) turns step 3 into `ComplexReverseIntertwinerKernelStatement`.
   For `ds` in the Langlands order, every `(𝔤, K)`-intertwiner `T` from the standard module of
   `ds` to that of `ds.reverse` vanishes on every proper `(𝔤, K)`-submodule. The Library proof
   cuts `ds` into blocks of tied exponents. It pairs `T w` against a block test vector with
   nonzero block Jacquet functional and uses tempered irreducibility at each tie (step 3) to show
   that `T w` vanishes at the long Weyl element `w₀`, and hence on `U(n)`. Its two block
   integration inputs are discharged inside that reduction by the Library theorems
   `complexBlockChartIntegrable` and `complexBlockParabolicIntegration`.
5. **The criterion.** `complexStandardIrreducibleCriterionReduction` (module
   `ComplexStandardIrreducibleCriterionReduction`) proves
   `ComplexStandardUnlinkedSwapStatement → ComplexReverseIntertwinerKernelStatement →
   ComplexStandardIrreducibleCriterionStatement`. Since `ds` is pairwise unlinked, it is reversed
   by adjacent swaps of unlinked characters. Composing the bijective intertwiners of step 2 gives
   an injective intertwiner `T` from the standard module of `ds` to that of `ds.reverse`. By
   step 4 every proper `(𝔤, K)`-submodule lies in `ker T = 0`. The standard module is nonzero by
   `complexStandardNontrivial` (module `ComplexStandardNontrivialProof`).

The route is the long-intertwining-operator argument suggested in the task context, factored into
rank-one swaps. The rank-one step is the `GL_2(ℂ)` irreducibility of step 1. The step "the image
of the long operator is irreducible" is replaced by the kernel statement of step 4.

## Prerequisites and independence

Every prerequisite is a proved Library theorem, and the composed theorem keeps none of them as a
premise. That includes the identification of the Library's standard module with the classical
principal series, `GL_2(ℂ)` irreducibility, intertwining and Langlands-quotient arguments, and
tempered irreducibility.

The task context forbids using `ComplexLargeStandardIrreducibleStatement` (V),
`ComplexLinkedLanglandsQuotientNotLargeStatement` (NL_C) or Vogan's theorem. A private
type-and-value closure scan checked this. It ran as a breadth-first search over the constants
used by the types and values of all constants reachable from
`complexStandardIrreducibleCriterion`, with theorem bodies included. The scan reached 79,385
constants, 5,500 of them in `Langlands`, and none of these 16:

- `ComplexLargeStandardIrreducibleStatement`, `complexLargeStandardIrreducible`;
- `ComplexLinkedLanglandsQuotientNotLargeStatement`, `complexLinkedLanglandsQuotientNotLarge`;
- `ComplexLargeStandardIrreducibleSplitStatement`, `complexLargeStandardIrreducibleSplit`;
- `ComplexLargeStandardIrreducibleReductionStatement`, `complexLargeStandardIrreducibleReduction`;
- `ComplexLargeLanglandsQuotientInjectiveStatement` (Vogan's theorem, V1′),
  `ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective`;
- `ComplexLargePrincipalSeriesStatement`, `complexLargePrincipalSeries`;
- `ComplexLargePrincipalSeriesReductionStatement`, `complexLargePrincipalSeriesReduction`,
  `complexLargeLanglandsQuotientInjective_of_principalSeries`.

As a positive control, the same scan run from `complexLargeStandardIrreducible` reaches V, NL_C,
the split statement and their proofs.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
