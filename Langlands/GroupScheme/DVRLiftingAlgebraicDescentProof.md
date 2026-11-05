# Proof that the DVR lifting property descends along algebraic field extensions

Author: Worker 254.

This module proves the published proposition
`Langlands.GroupScheme.DVRLiftingAlgebraicDescentStatement.{u}` from
`Langlands.GroupScheme.DVRLiftingAlgebraicDescentStatement`.

## Result

`dvrLiftingAlgebraicDescentStatement : DVRLiftingAlgebraicDescentStatement.{u}`.
Let `k L : Type u` be fields with `[Algebra k L]` and `[Algebra.IsAlgebraic k L]`,
and let `X : Over (Spec (CommRingCat.of k))`. If the base change of `X` along
`Spec.map (CommRingCat.ofHom (algebraMap k L))`, formed with `Over.pullback`, has
`PseudoComplete.HasDVRLifting` over `L`, then `X` has
`PseudoComplete.HasDVRLifting` over `k`. There are no hypotheses on `X`.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition C.1.2(2), first assertion and its proof, printed pp.582–583
(PDF pp.608–609), registered as `conrad-gabber-prasad-2015-pseudo-reductive`.
The statement is the valuative (existence) part of that assertion, specialized
to algebraic extensions. The paired Markdown of the statement module explains
this in detail.

## Implemented proof

The theorem introduces `k`, `L`, the instances, `X` and the hypothesis `h`, and
applies `PseudoComplete.hasDVRLifting_of_baseChange k L X h` from
`Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange`. That theorem has
exactly the hypothesis and conclusion of the statement, so nothing else is
needed. Its Markdown describes the argument:

1. Pass from a DVR `R` over `k` to the localization `R'` of `L ⊗[k] R` at a
   prime containing `1 ⊗ ϖ`, where `ϖ` is a uniformizer. This is
   `Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange`: `R'` is a DVR with
   residue field geometrically reduced over `L`, and `R → R'` is injective and
   local.
2. Lift the generic-point morphism over `L` by the hypothesis `h`.
3. Descend the lift to `Spec R` by the domination property
   `X(R) = X(R') ∩ X(K)` from `Langlands.GroupScheme.PseudoCompleteDomination`.
