# Genuine smooth vectors in invariant Hilbert subspaces

This module is internal infrastructure for the proof of
`CuspidalOperatorMultiplicityOneStatement`. It restricts a supplied representation by bounded complex operators to a
supplied invariant subspace of a complex inner product space. It then compares the
genuine smooth vectors, genuine orbit derivatives, word seminorms and genuine
derivative topology of the restriction with those of the ambient representation. All
declarations are in the namespace `Langlands.Archimedean.SmoothInvariantSubspace`.

## Setting and supplied hypotheses

The data are a group `G`, a complex normed space `E` with `[InnerProductSpace ℂ E]`, a
homomorphism `π : G →* (E →L[ℂ] E)`, a submodule `U : Submodule ℂ E`, and an invariance
hypothesis `hU : ∀ g v, v ∈ U → π g v ∈ U`. Other hypotheses appear only where they are
used:

- `[TopologicalSpace G]` and the model `I : ModelWithCorners ℝ 𝔤 H` with
  `[ChartedSpace H G]` are used for smoothness of orbit maps.
- `[CompleteSpace U]` provides Mathlib's orthogonal projection onto `U`. It is used for
  the converse smoothness implication, the exact range and its closedness, and the
  continuous linear equivalence. A complete subspace is closed in `E`. `E` itself need
  not be complete.
- `[LieGroup I ∞ G]` is needed for the published derived operators and the derivative
  topology. It is needed only from the derived operators on smooth vectors onward.
- `IsContinuousRepresentation π` and `∀ g, Isometry (π g)` are supplied only as the
  premises of the two transfer lemmas. Nothing else uses them. In particular, the
  smoothness equivalence assumes neither unitarity nor joint continuity.

The universes of the model vector space `𝔤`, the model space `H`, the group `G` and the
carrier `E` are independent.

## The restricted representation

`restriction π U hU : G →* (U →L[ℂ] U)` sends `g` to Mathlib's restriction
`(π g).restrict (hU g)` of the bounded operator to the invariant subspace. It
respects the identity and products because `π` does, checked pointwise after
coercion to `E`. `restriction_apply` is the ambient agreement
`(restriction π U hU g v : E) = π g v`, which holds by `rfl`.

`isometry_restriction` transfers a supplied isometry hypothesis. The distance on `U`
is that of `E`, so the hypothesis for `π g` applies to the coerced vectors.
`isContinuousRepresentation_restriction` transfers joint continuity of `(g, v) ↦ π g v`.
The restricted action map is the ambient one composed with `(g, v) ↦ (g, (v : E))`,
and it takes values in `U`, so it is continuous into the subtype.

## Genuine smoothness

Smoothness is the published `IsSmoothVector I π v`: the orbit map
`orbitMap π v = (g ↦ π g v)` is real `C^∞` from `G` to `E`.

- `isSmoothVector_coe`: if `v : U` is smooth for the restriction, then `(v : E)` is
  smooth for `π`. The ambient orbit map is the restricted orbit map followed by the
  bounded inclusion `U.subtypeL`, viewed as real linear. This holds definitionally.
  A continuous linear map is smooth, so the composite is smooth. Completeness is not
  used.
- `isSmoothVector_of_coe` (with `[CompleteSpace U]`): if `(v : E)` is smooth for `π`,
  then `v` is smooth for the restriction. The restricted orbit map equals the ambient
  orbit map followed by the orthogonal projection `U.orthogonalProjectionOnto`. This
  is because every `π g v` already lies in `U`, and the projection fixes vectors of
  `U` (`orthogonalProjectionOnto_mem_subspace_eq_self`). The projection is a bounded
  real-linear map, so the composite is smooth. The projection is applied only to
  vectors already in `U`. The proof neither uses nor claims that projection commutes
  with `π` on all of `E`, which can fail when `π` is not unitary.
- `isSmoothVector_iff` combines the two implications.

## Inclusion of smooth vectors and genuine derivatives

`smoothInclusion π U hU I` is the complex-linear map from
`smoothVectors I (restriction π U hU)` to `smoothVectors I π` given by coercion. It
is well defined by `isSmoothVector_coe`. `smoothInclusion_apply` records that it is
coercion.

`lieDerivative_coe` states that for a restricted smooth vector `v` and `X : 𝔤`,
`lieDerivative I π X (v : E)` is the coercion of `lieDerivative I (restriction π U hU) X v`.
Here `lieDerivative` is the published derivative at the identity of the orbit map in
direction `X`. The proof writes the ambient orbit map as the bounded inclusion
composed with the restricted orbit map. The manifold chain rule `mfderiv_comp` then
applies, with the derivative of a continuous linear map being itself.
Differentiability at the identity comes from smoothness. Like the published
`SmoothDerivative` module, it uses the local option
`backward.isDefEq.respectTransparency false` to close the final definitional
unfolding.

With `[LieGroup I ∞ G]`:

- `smoothInclusion_smoothLieDerivative` restates this for the published derived
  operator `smoothLieDerivative` on smooth vectors.
- `smoothInclusion_smoothIteratedLieDerivative` extends it to every word `Xs : List 𝔤`
  of derived operators. The proof is by induction on the word, following the
  published recursion.
- `iteratedLieDerivative_coe` is the same identity for the underlying vectors
  `iteratedLieDerivative`.
- `wordSeminorm_smoothInclusion` proves exact equality of the published word
  seminorms: `wordSeminorm I π Xs (smoothInclusion … v) = wordSeminorm I (restriction π U hU) Xs v`.
  Both sides are the norm of the same word derivative, and the norm on `U` is that of
  `E`.

## Derivative topology

The genuine derivative topology is the published one on `DerivativeSmoothVectors I π`.
That type is a copy of the smooth vectors, topologized by the injective coordinate map
`derivativeCoordinates` into `List 𝔤 → E`, which sends a vector to all of its word
derivatives.

- `derivativeInclusionLinear` and `derivativeInclusion` transport `smoothInclusion`
  through the published `toSmooth` equivalences.
  `toSmooth_derivativeInclusionLinear` and `toSmooth_derivativeInclusion` record this.
- `derivativeCoordinates_derivativeInclusionLinear`: each ambient coordinate of the
  image is the coerced coordinate of the original vector. This is
  `iteratedLieDerivative_coe`.
- `continuous_derivativeInclusionLinear`: the topology on the target is induced, so it
  suffices that each ambient coordinate is continuous. By the previous item, that
  coordinate is the published continuous coordinate `derivativeCLM` of the restricted
  representation, followed by the inclusion `U → E`. `derivativeInclusion` bundles the
  map as a continuous complex-linear map.
- `isEmbedding_derivativeInclusion`: ambient coordinates composed with the inclusion
  equal restricted coordinates composed with the coordinatewise inclusion
  `(List 𝔤 → U) → (List 𝔤 → E)`. That map is an embedding by
  `IsEmbedding.piMap` of subtype embeddings. Both coordinate maps are embeddings, so
  `IsEmbedding.of_comp_iff` shows that the inclusion is an embedding. No completeness
  is used.
- `mem_range_derivativeInclusion` (with `[CompleteSpace U]`): an ambient smooth vector
  is in the range exactly when its underlying vector lies in `U`. Every image has this
  property. Conversely, such a vector is a restricted smooth vector by
  `isSmoothVector_of_coe`, and its inclusion is the given vector.
- `isClosedEmbedding_derivativeInclusion` (with `[CompleteSpace U]`): the range is the
  inverse image of `U` under the continuous empty-word coordinate `derivativeCLM I π []`.
  `U` is closed because it is complete, so the range is closed. Together with the
  embedding, this gives a closed embedding.

## The ambient subspace and the continuous linear equivalence

`ambientSmoothSubspace π U I` is the submodule of `DerivativeSmoothVectors I π` whose
underlying vectors lie in `U`. It is the inverse image of `U` under the empty-word
coordinate. Membership is characterized by `mem_ambientSmoothSubspace`.
`isClosed_ambientSmoothSubspace` shows that it is closed in the derivative topology
whenever `U` is closed in `E`.

With `[CompleteSpace U]`:

- `range_derivativeInclusion` states the exact range as an equality of submodules:
  `(derivativeInclusion π U hU I).range = ambientSmoothSubspace π U I`.
- `derivativeEquivLinear` is the bijective corestriction of the inclusion to this
  submodule. It is injective because the inclusion is an embedding, and surjective by
  the range description.
- `derivativeEquiv` is a continuous linear equivalence
  `DerivativeSmoothVectors I (restriction π U hU) ≃L[ℂ] ambientSmoothSubspace π U I`.
  Continuity forward is continuity of the inclusion into a subtype. Continuity of the
  inverse follows because the inclusion is an embedding, and the inclusion composed
  with the inverse is the subtype coercion.
- `derivativeEquivLinear_apply`, `coe_derivativeEquiv_apply` and
  `derivativeInclusion_derivativeEquiv_symm_apply` record that the equivalence and its
  inverse are computed by the inclusion.

## Provenance and scope

The results are internal consequences of the published smooth-vector,
genuine-derivative and derivative-topology constructions in `SmoothVectors`,
`SmoothDerivative` and `SmoothDerivativeTopology`. They also use Mathlib's
restriction of continuous linear maps, orthogonal projection onto a complete subspace,
manifold chain rule and induced and product topologies. They formalize the standard
fact that a vector of a closed invariant subspace is smooth for the
subrepresentation exactly when it is smooth in the ambient space, with the
corresponding comparison of the smooth topologies. No literature statement is
transcribed.

The module does not assert that the inherited norm topology on smooth vectors equals
the derivative topology. It assumes no unitarity and does not use projections that
intertwine `π`. It proves nothing about actual cuspidal actions, density of
compact-finite vectors, extension of functionals, Whittaker models or multiplicity
one.
