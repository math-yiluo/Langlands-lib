# Actual completed valuation rings in curve-place extensions

This module restricts the constructed completion embeddings to the actual
completed valuation rings, proves compatibility with the original valuation
rings and their residue fields, and proves preservation of ramification index
and inertia degree. The original ramification-inertia product is consequently
bounded by the completed field degree.

These are derived arithmetic inputs for Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed page 10.
That passage uses completed integer rings for the integral-point comparison
and finite extensions of completed fields for the field-valued comparison.
This unit supplies the actual ring and residue maps and the local degree
bound; the global integral models and the simultaneous tensor decomposition
remain separate.

## Actual fields, places and scalar actions

Let `k`, `K` and `L` be fields in one arbitrary common universe, with
`Algebra k K`, `Algebra k L` and `Algebra K L`. Fix
`p : AlgebraicCurve.Place k K` and `q : CurvePlacesAbove k L p`.
Thus `q.val` is an actual upper discrete curve place whose valuation subring
restricts exactly to that of `p`.

Write `K_p` and `L_q` for `curvePlaceCompletion p` and
`curvePlaceCompletion q.val`; write `O_p` and `O_q` for their existing
`curvePlaceCompletionIntegers` valuation subrings. The original lower and
upper valuation rings are `p.toValuationSubring` and
`q.val.toValuationSubring`. All of these are the existing actual rings.
The field embedding and its scalar action are imported from
`Langlands.Global.CurvePlaceCompletionExtension`.

Everything except the final finite-degree bound is proved without a
finite-extension hypothesis. The bound additionally assumes
`[FiniteDimensional K L]`. There is no separability, finite-constant-field,
`FunctionField`, rational parameter or compatible constant-field-tower
hypothesis.

All declarations below are in
`Langlands.Global.CurvePlaceCompletedIntegersExtension`.

## Completed integral map and local structure

`completionMap_mem_integers_iff` proves

```text
completionMap p q x ∈ O_q ↔ x ∈ O_p.
```

For the original field elements this is the exact upper-place restriction
law, together with the existing original-field/completion integrality
comparison. To extend it to every element of `K_p`, the proof uses density
of `K` and closedness of the equivalence between the two clopen
valuation-ring predicates. Continuity of the original completion map gives
the upper predicate's clopen preimage.

`completionIntegersMap p q : O_p →+* O_q` restricts that original completion
map. `completionIntegersMap_coe` identifies its underlying field map.
`continuous_completionIntegersMap` uses the existing subspace topologies on
both valuation rings. `completionIntegersMap_original` proves that mapping
an original lower integer into its completion and then applying this map
equals first mapping it to the original upper valuation ring and then
completing it.

Scoped instances give `O_p` its compatible actions on `L_q` and `O_q`, and the
two scalar towers through `K_p` and `O_q`. The algebra instances have low
priority to preserve existing own-field structures.
`completionIntegersMap_mem_maximalIdeal_iff` proves exact restriction of
maximal ideals. Its proof characterizes a valuation-ring nonunit as zero or
failure of its inverse to be integral, then uses injectivity and the proved
integrality equivalence. This yields the scoped local-homomorphism instance
and torsion freeness of `O_q` over `O_p`.

`originalLocalHom` similarly gives the original valuation-ring map its local
homomorphism instance, using the imported original maximal-ideal
`LiesOver` result.

## Canonical residue fields and inertia degree

The existing `curvePlaceCompletionResidueEquiv` identifies each original
place residue field with the residue field of its actual completed valuation
ring. `completionResidueEquiv_algebraMap` proves that the square of these two
equivalences and the original and completed residue-field embeddings
commutes. The proof represents a residue class by an original integer,
uses the existing reduction formulas, and applies
`completionIntegersMap_original`.

`completionIntegers_inertiaDeg` proves

```text
(maximalIdeal O_q).inertiaDeg O_p
  = q.val.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring.
```

Both inertia degrees are rewritten as dimensions of the corresponding
residue-field extensions. The commuting equivalences identify these
dimensions by `Algebra.finrank_eq_of_equiv_equiv`.
This proof works without finite residue cardinalities and introduces no
finite-constant-field premise.

## Valuation normalization and ramification index

`valuation_completionMap` identifies the valuation of the image of an
arbitrary completed lower element with its lower valuation raised to the
original ramification index. On original field elements this is Mathlib's
general `HeightOneSpectrum.valuation_liesOver` theorem for the actual two
valuation rings and their maximal ideals. The identity extends to the
completions by density and continuity of the surjective adic valuations.

`completionIntegers_intValuation` identifies the normalized adic valuation
of the maximal ideal of `O_p` with the existing completed-field valuation
on its integral elements. For a nonzero integer, the proof writes it as a
unit times a power of an irreducible uniformizer. Both valuations take the
unit to one and the uniformizer to `WithZero.exp (-1)`.

`completionIntegers_ramificationIdx` proves

```text
(maximalIdeal O_q).ramificationIdx O_p
  = q.val.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring.
```

It applies `HeightOneSpectrum.intValuation_liesOver` to a uniformizer of
`O_p`. The valuation normalization and `valuation_completionMap` then give
equal powers of `WithZero.exp (-1)`, so their exponents are equal.

With `[FiniteDimensional K L]`, `localDegree_lowerBound` proves

```text
q.val.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring
  * q.val.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring
    ≤ finrank K_p L_q.
```

The imported completion embedding already supplies finite local degree.
The proof applies the published general
`Langlands.LocalField.dvrDegreeLowerBound` to `O_p`, `O_q`, `K_p` and `L_q`,
then rewrites both completed invariants using the comparisons just proved.

## Provenance and remaining work

Source ID: `conrad-2011-weil-grothendieck-adelic-points`.
The registered 21-page original has SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The cited locator is Example 4.2, printed page 10: completed integer rings,
the product of completed field extensions and the local Weil comparison.

The normalization and ramification arguments generalize the existing
number-field implementations in
`Langlands.Global.AdelicFunctoriality.CompletedRamification`.
The residue-dimension argument uses the actual general curve-place residue
equivalence rather than the number-field residue-cardinality argument.
Thus these are derived arithmetic constructions and comparisons, rather
than additional assertions attributed verbatim to Conrad.

No finiteness theorem for a global integral closure, fundamental degree-sum
equality, tensor injectivity, global integral-model comparison or adelic
limit comparison is proved here. These remain obligations of the
whole-paper task.
