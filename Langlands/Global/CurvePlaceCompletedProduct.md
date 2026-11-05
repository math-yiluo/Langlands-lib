# Finiteness and canonical completed products at actual curve places

This module proves finiteness of the full set of upper discrete curve places in
a finite field extension and constructs the canonical surjective tensor map to
the product of all their existing completions. It is derived arithmetic
infrastructure for Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 4.2, printed page 10. That passage decomposes the
completed tensor algebra into the product over all upper places.

This unit supplies the full finite index set and surjectivity of that
comparison. Tensor injectivity, which is needed for the decomposition used in
the source, remains a separate obligation. It is not assumed or claimed here.

## Actual objects and hypotheses

The fields `k`, `K` and `L` lie in one arbitrary common universe `u`, with
`Algebra k K`, `Algebra k L` and `Algebra K L`. A lower place is an actual
`p : AlgebraicCurve.Place k K`. The existing
`Langlands.Global.CurvePlacesAbove k L p` consists of all actual upper curve
places whose valuation subring restricts to exactly the lower one.

Write `K_p` for `p.heightOneSpectrum.adicCompletion K` and `L_q` for
`q.val.heightOneSpectrum.adicCompletion L`. The scalar action of `K_p` on `L_q`
is the constructed original completion embedding from
`Langlands.Global.CurvePlaceCompletionExtension`; its scoped instances are used
throughout the tensor comparisons.

The family index `ι` lies in an independently arbitrary universe `v`. The
canonical family map can be defined for any `q : ι → CurvePlacesAbove k L p`.
Density requires a finite index and injectivity of that family. Surjectivity,
degree bounds and finiteness of the full upper-place subtype additionally
require `[FiniteDimensional K L]`. No separability, finite constants,
rational-function presentation, `FunctionField` instance or compatibility of
the constant-field tower is a premise of this module.

## Absolute values and weak approximation

In the namespace `Langlands.Global.CurvePlaceCompletedProduct`,
`absoluteValue q` realizes an actual curve place's discrete valuation as a real
absolute value. It uses the existing base-two rank-one realization.
`absoluteValue_nontrivial` proves nontriviality.
`absoluteValue_isEquiv_iff` proves that two such absolute values are equivalent
exactly when their actual curve places are equal. The proof recovers the
valuation comparison preorder, then the valuation subring, and applies
`AlgebraicCurve.Place.ext`.

`withAbsEmbedding q` is the original field map to the actual adic completion,
with source `WithAbs (absoluteValue q)`.
`continuous_withAbsEmbedding` proves continuity using two existing uniform
comparisons: from the absolute value to its associated nonarchimedean
valuation, then from that valuation to the equivalent original adic valuation.
The canonical embedding into the underlying completion and its wrapper
comparison finish the proof. `withAbsEmbedding_denseRange` reuses density of
the original field in its actual adic completion.

`denseRange_family` applies to any finite family of distinct actual curve
places of `L`, independently of any lower place. It proves density of the
original diagonal

```text
L → (∀ i, (q i).heightOneSpectrum.adicCompletion L).
```

The proof uses Mathlib's abstract weak approximation theorem
`AbsoluteValue.denseRange_algebraMap_pi` for nontrivial, pairwise inequivalent
real absolute values. A product of the continuous dense maps
`withAbsEmbedding` then gives density in the actual completed fields. These
fields carry their original completion topologies and the ordinary product
topology.

## Canonical family tensor map and degree bounds

For a family `q : ι → CurvePlacesAbove k L p`,

```text
familyTensorMap p q : K_p ⊗[K] L →ₐ[K_p] (∀ i, L_(q i))
```

is the product of the existing individual canonical tensor maps. The formula
`familyTensorMap_tmul` retains both original field maps:

```text
familyTensorMap p q (a ⊗ₜ[K] x) i
  = CurvePlaceCompletionExtension.completionMap p (q i) a
      * algebraMap L L_(q i) x.
```

For a finite injective family, `familyTensorMap_denseRange` follows from weak
approximation because tensors `1 ⊗ₜ[K] x` give the original diagonal.
With `[FiniteDimensional K L]`, `familyTensorMap_surjective` proves that this
image is closed and hence equal to the full product. Its linear image is
finite dimensional over the complete lower completion. As in the individual
completion construction, an explicit rank-one norm on `K_p` retains its
existing uniform structure. The target product has the existing continuous
scalar action and Hausdorff topology, so
`Submodule.closed_of_finiteDimensional` applies.

For a finite enumerated injective family, `familyLocalDegree_sum_le` proves

```text
∑ i, finrank K_p L_(q i) ≤ finrank K L.
```

This is the dimension inequality of the proved surjective linear map, using
dimension under base change and the dimension of a finite product. Each upper
completion is a nontrivial field and has finite dimension by the imported
individual local-degree construction. Its local degree is therefore at least
one. Summing these inequalities gives `family_card_le`:
the cardinality of the family is at most `finrank K L`.

## Full upper-place subtype and simultaneous map

`Langlands.Global.curvePlacesAbove_finite` proves that
`CurvePlacesAbove k L p` is finite. If it were infinite, it would contain a
finite subset of cardinality `finrank K L + 1`. Applying `family_card_le` to
that subset gives a contradiction. Thus no finiteness hypothesis on the set of
all upper places is supplied.

`curvePlacesAbove_fintype` enumerates this full subtype only after the
finiteness proof. It does not select or discard any upper places.
`allTensorMap p` specializes `familyTensorMap` to the identity family of the
full subtype. `allTensorMap_tmul` states its original component formula.
`allTensorMap_surjective` specializes the proved finite-family surjectivity,
and `allLocalDegree_sum_le` gives the corresponding bound summed over every
actual upper place.

The definition `allTensorMap` itself does not require finite dimensionality;
its surjectivity theorem and the full-subtype finiteness instances do.
The finiteness proof does not require nonemptiness. Under a compatible
constant-field tower, nonemptiness is available separately from the imported
completion-extension module.

## Provenance and remaining comparison

Source ID: `conrad-2011-weil-grothendieck-adelic-points`.
The registered 21-page original has SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The cited locator is Example 4.2, printed page 10, the completed-tensor product
over all upper places.

The source uses a tensor algebra isomorphism for global fields. The present
more general finite-extension construction proves only the stated
surjectivity and finiteness results, by weak approximation and
finite-dimensional topology. Its canonical maps and local scalar actions are
actual constructions; no comparison equivalence or local-degree bound is
given as an additional premise.

Injectivity in the function-field setting, the resulting algebra
decomposition, the associated nonaffine point-space homeomorphism, integral
models and passage to adelic limits remain obligations of the whole-paper
task.
