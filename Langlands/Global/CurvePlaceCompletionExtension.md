# Actual completion embeddings at upper curve places

This module constructs the actual completion embeddings and proves finite local
degree for finite extensions of fields equipped with discrete curve places.
It supplies arithmetic inputs for the function-field case of Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed page 10. That passage uses the completions at all places
above a lower place, their finite extensions of the lower completion, and the
simultaneous completed-tensor decomposition.

The present construction is derived infrastructure for that passage. It works
over an arbitrary constant field and does not require a rational-function-field
presentation. The simultaneous decomposition and the adelic comparison are
separate obligations.

## Fields, places and original valuation rings

Let `k`, `K` and `L` be fields in independently arbitrary universes, with
`Algebra k K`, `Algebra k L` and `Algebra K L`. Let
`p : AlgebraicCurve.Place k K`. These existing places contain an actual
nontrivial discrete valuation subring of the field, containing the constants;
their `heightOneSpectrum` is the maximal ideal of that subring.

`Langlands.Global.CurvePlacesAbove k L p` is the full subtype

```text
{q : AlgebraicCurve.Place k L //
  q.toValuationSubring.comap (algebraMap K L) = p.toValuationSubring}.
```

Thus it contains every actual upper curve place with exactly the prescribed
restriction of valuation subrings. No finite set or chosen list of upper places
is supplied. In what follows, write `q` for an element of this subtype,
`K_p` for `p.heightOneSpectrum.adicCompletion K`, and `L_q` for
`q.val.heightOneSpectrum.adicCompletion L`.

The declarations in `Langlands.Global.CurvePlaceCompletionExtension` have
parameters `p` and `q`. `mem_iff` states that the original field embedding
belongs to the upper valuation subring exactly when its input belongs to the
lower valuation subring. `integersMap` is the resulting restriction
`p.toValuationSubring →+* q.val.toValuationSubring` of `algebraMap K L`.

Scoped instances in this namespace give the lower valuation ring its original
actions on `L` and on the upper valuation ring, their two scalar towers, and
torsion freeness of the upper valuation ring over the lower one. The two
valuation-ring algebra instances have lower priority than the existing
own-field instances, preserving the canonical fraction-field structures.
The maximal ideal of the upper valuation ring is proved to lie over the lower
maximal ideal. Its proof uses the characterization of nonunits by zero or
failure of the inverse to belong to the valuation ring, together with `mem_iff`
and injectivity of the field embedding.

## Completion map and continuous scalar action

`uniformContinuous_withVal` proves uniform continuity of the original embedding
between `WithVal p.adicValuation` and `WithVal q.val.adicValuation`. It applies
Mathlib's general
`IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver`
to the actual two valuation rings and their maximal ideals. This is a general
Dedekind-domain result and introduces no number-field hypothesis.

`completionMap p q : K_p →+* L_q` extends this embedding using
`UniformSpace.Completion.mapRingHom` and the existing ring equivalences between
each adic-completion wrapper and its underlying valued-field completion.
`continuous_completionMap` proves continuity for the original completion
topologies. The formula `completionMap_algebraMap` is

```text
completionMap p q (algebraMap K K_p x)
  = algebraMap L L_q (algebraMap K L x).
```

In particular this is the completion of the original field embedding.
As a unital ring homomorphism between fields, it is injective. The module does
not define an endpoint topology by transporting it through this embedding.

Further scoped instances use this map as `Algebra K_p L_q`, prove
`IsScalarTower K K_p L_q`, and prove `ContinuousSMul K_p L_q`.
The last proof expresses scalar multiplication as the continuous completion
map followed by multiplication in `L_q`. These constructions require neither
finite dimensionality nor `IsScalarTower k K L`.

## Canonical tensor map and finite local degree

`tensorMap p q : K_p ⊗[K] L →ₐ[K_p] L_q` is the algebraic tensor lift of the
completion embedding and the original map `L → L_q`. Its formula
`tensorMap_tmul` is

```text
tensorMap p q (a ⊗ₜ[K] x)
  = completionMap p q a * algebraMap L L_q x.
```

`tensorMap_denseRange` needs no finite-extension hypothesis: the image contains
the dense original field `L`, using the tensors `1 ⊗ₜ[K] x`.

With the additional hypothesis `[FiniteDimensional K L]`,
`tensorMap_surjective` proves surjectivity. The tensor domain and therefore the
linear image are finite dimensional over `K_p`. The lower completion has its
existing complete topology; a rank-one norm is obtained from its discrete
valuation by `Valuation.IsRankOneDiscrete.rankOne` and
`Valued.toNontriviallyNormedField`. This norm retains the given uniform
structure. The image is consequently closed by
`Submodule.closed_of_finiteDimensional`. Closedness and the proved density
make the image all of `L_q`.

The scoped instance `localFinite` then proves `Module.Finite K_p L_q` by
`Module.Finite.of_surjective`. It uses the constructed scalar action. No
finite-local-degree premise, tensor surjectivity premise, separability
hypothesis or finite-constant-field hypothesis is supplied.

Outside the namespace, `curvePlacesAbove_nonempty` additionally assumes
`IsScalarTower k K L` and `[FiniteDimensional K L]`. It uses the existing
`curvePlaceExtension` and its exact `curvePlaceExtension_comap` theorem to
produce an element of the full upper-place subtype. This is the only
declaration here requiring compatibility of the constant-field tower.

## Source and retained scope

Source ID: `conrad-2011-weil-grothendieck-adelic-points`.
The registered 21-page original has SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The cited locator is Example 4.2, printed page 10, the completed-tensor
decomposition and reduction to finite extensions of complete fields.
The implemented dense-image and closed-subspace argument makes explicit the
finite-local-degree input of that reduction.

The actual curve places and their completions come from the existing
`AlgebraicCurve.Place` and Mathlib adic-completion constructions.
Place extension is reused from `Langlands.Global.CurvePlaceExtension`.
The module does not prove finiteness of `CurvePlacesAbove`, bijectivity of the
map to the simultaneous product, the function-field point homeomorphism,
integral-model compatibility or passage to adelic limits. All remain
obligations of the whole-paper task.
