# Finite triangular translations preserve product measures

Author: Worker 86.

This module proves the published proposition
`Langlands.HarmonicAnalysis.FiniteTriangularTranslationStatement`.
The application theorem is
`Langlands.HarmonicAnalysis.measurePreserving_finiteTriangularTranslation`;
the closing theorem `Langlands.HarmonicAnalysis.finiteTriangularTranslation`
has exactly the published proposition as its complete type, with independent
index and coordinate universe levels.

## Hypotheses and conclusion

Let `ι` be a finite type and `X i` a dependent family of additive commutative
groups with measurable spaces and jointly measurable addition. Each coordinate
measure `μ i` is sigma-finite and invariant under left addition. Given any
natural-valued rank function and a measurable map `f` on the dependent product,
assume that `f x i` depends only on coordinates of strictly lower rank than
`i`. Then `x ↦ (fun i => f x i + x i)` preserves `Measure.pi μ`.

The proof allows an empty index type, repeated ranks and zero coordinate
measures. It requires no topology, normalization, standard Borel structure,
nonzero measure or injectivity of the rank function.

## Implemented proof

First, a private lemma handles a single coordinate `i`. Suppose the measurable
translation term `g x : X i` is unchanged when only `x i` is replaced. The map
`x ↦ Function.update x i (g x + x i)` is measurable. To show that its pushforward
is the original measure, the proof compares integrals of the indicator of an
arbitrary measurable set. Mathlib's `lintegral_eq_of_lmarginal_eq` reduces this
to equality of the marginal integrals in coordinate `i`. By
`lmarginal_singleton`, these are ordinary one-coordinate integrals with all
other coordinates fixed. Independence of `g` from coordinate `i` makes the
inner map an actual constant left translation. The identity follows from
`measurePreserving_add_left` and its integral change-of-variables theorem.
Sigma-finiteness is used by the marginal integration theorem; no positivity
or division by a measure occurs.

Next, the proof establishes preservation for the partial map that translates
exactly the coordinates in a finite subset `s`. It uses strong induction on
finite subsets. The empty case is the identity. For a nonempty `s`, choose an
index `i` of minimum rank in `s`, apply the induction hypothesis to `s.erase i`,
and then apply the single-coordinate translation at `i`. Every coordinate
strictly below `rank i` is outside `s.erase i`, so its value is unchanged by
the partial map. The dependence hypothesis therefore gives the same `i`th
translation term before and after that partial map. Also, `i` itself has not
yet changed. Coordinatewise equality identifies this composition with the
partial map for `s`. Taking `s` to be all indices proves the theorem.

This recursion applies higher-rank translations first. Equal-rank coordinates
may occur in either order, because the dependence hypothesis is strict. The
closing theorem introduces precisely the published hypothesis telescope and
applies the named application theorem.

## Provenance and scope

This is an internal finite-product measure lemma, motivated by the upper block
unipotent application described in the unchanged statement's Markdown. It is
not a transcription of a literature theorem. The singleton marginal argument
uses the same general integration mechanism as Mathlib's
`Real.volume_preserving_transvectionStruct`, adapted here to arbitrary
dependent coordinate groups and translation-invariant sigma-finite measures.
The finite-rank induction is implemented directly in this module.

The result does not construct block coordinates, prove their multiplication
formulas, normalize p-adic Haar measure, or compute determinant scaling. Those
remain the responsibilities of the application.
