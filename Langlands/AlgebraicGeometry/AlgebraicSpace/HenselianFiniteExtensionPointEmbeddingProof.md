# Rational points embed along finite extensions of henselian valued fields

Authors: Worker 157, with an adaptation of Worker 105's published completion
embedding argument for the case of trivial relative separable closure.

`henselianFiniteExtensionPointEmbedding` proves exactly
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFiniteExtensionPointEmbeddingStatement.{u}`.
It imports the unchanged published statement and retains all its hypotheses:
`K` and `L` are henselian nontrivially normed fields with `NormedAlgebra K L`
and `FiniteDimensional K L`, and `X` is quasi-separated, locally separated
and locally of finite type over `Spec K`. The conclusion is an embedding for
the two independently defined étale-chart topologies.

The assertion is the finite-degree supplement to Proposition 5.11(3) on printed
p.19 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implemented proof is a derived direct argument with étale charts and
finite Galois descent. It does not use Conrad's Weil-restriction argument,
the unrestricted Proposition 5.11(1), or completeness.

The map `fieldExtensionPointMap K L X`, from
`FiniteExtensionPointEmbeddingReduction`, is definitionally the target's map:
change the value ring along `K → L`, then apply
`(baseChangeRingPointsEquiv K L L X).symm`. That module supplies continuity
for arbitrary normed extensions, compatibility with base-changed chart maps,
local separatedness after base change, and the canonical tower identities.
Although it also contains a conditional completion reduction, the present
proof uses its point-map infrastructure directly.

## Norms and henselianity

`FiniteExtensionEmbedding.isometry_algHom` proves that an embedding of an
algebraic normed extension of henselian `K` into another normed `K`-extension
is an isometry. Pulling back the target norm gives an absolute value on the
source extending the norm of `K`; uniqueness in `IsHenselianValuedField`
identifies it with the source norm. `isometry_aut` is the automorphism case.

`isHenselianValuedField_extension` proves that an algebraic normed extension
of a henselian valued field is henselian. Given an algebraic tower `E/L/K`,
the unique absolute value on `E` extending the norm of `K` restricts to the
given norm on `L`, by uniqueness over `K`. Any two extensions of the norm
of `L` also extend the norm of `K`, so are equal.

## Trivial relative separable closure

`exists_rational_of_extension` generalizes the rationality lemma in
`HenselianCompletionPointEmbeddingProof`. Assume `separableClosure K L = ⊥`.
If an `L`-point of an étale chart and a `K`-point of another chart have the
same image in `X(L)`, they determine an `L`-point of the represented chart
overlap. Its projection to the second chart is étale, hence formally
unramified. The published
`exists_changeRing_eq_of_formallyUnramified` makes that point rational.
The coefficient-change embedding on scheme points identifies its second
projection with the original `K`-point.

`isEmbedding_of_separableClosure_eq_bot` applies this to the chart topology.
Every point of `X(K)` lifts to a finite-type étale chart. An open subset of
`X(K)` pulls back to an open subset in each chart, which extends to an open
subset of the corresponding chart over `L`, because scheme coefficient
change is an embedding. Their images are open over henselian `L`.
Rationality of every lift over a rational point makes the preimage of their
union exactly the original open subset. It also proves injectivity of the
point map. This step uses quasi-separatedness and local finite type of `X`,
henselianity of `L`, and the explicit relative-separable-closure premise;
it does not require local separatedness.

## The finite Galois case

`isEmbedding_of_isGalois` uses local separatedness to prevent two nearby
conjugate chart lifts from having the same image.

Let `W` be open in `X(K)` and `x ∈ W`. The published rational-point étale
lifting theorem gives an affine finite-type étale chart `c : U → X` and
`u ∈ U(K)` above `x`. Write `i : U(K) → U(L)` for coefficient change and
`q : U(L) → X_L(L)` for the base-changed chart map.

Scheme coefficient change is an embedding, so choose an open `A ⊆ U(L)`
whose preimage under `i` is `c⁻¹(W)`. Local separatedness after base change
and `exists_isOpen_injOn_schemePointsMap` give an open neighborhood `V` of
`i(u)` on which `q` is injective. For each `σ ∈ Gal(L/K)`, coefficient
change by `σ` gives a continuous map `r_σ` on `U(L)` and fixes `i(u)`.
Use the open neighborhood

```
E = (A ∩ V) ∩ ⋂ σ ∈ Gal(L/K), r_σ⁻¹(V).
```

There are finitely many automorphisms, so `E` is open. The map `q` is open:
the scheme base-change equivalence is a homeomorphism and the chart map
over henselian `L` is open. Thus `q(E)` is an open neighborhood of the image
of `x`.

If `q(η)` for `η ∈ E` is the image of a rational point `y ∈ X(K)`, all
`r_σ(η)` have the same image. They and `η` lie in `V`, where `q` is
injective, hence `η` is Galois invariant. The published
`GaloisChartPoint.exists_desc_of_galois_invariant` descends it to a point
of the affine scheme `U(K)`. Membership in `A` puts that point in
`c⁻¹(W)`. Injectivity of coefficient change on space points then shows
`y ∈ W`.

Consequently each `x ∈ W` has an open target neighborhood whose preimage
lies in `W`. Taking their union proves the inducing property. Injectivity
is the published fppf-sheaf injectivity for finite field extensions.

## Finite separable and arbitrary finite extensions

`isEmbedding_of_isSeparable` embeds a finite separable extension `L/K` in
a finite Galois extension `N/K`. Henselianity of `K` supplies its extending
absolute value; this defines a nontrivially normed field `N` and a normed
`K`-algebra structure. The embedding of `L` into `N` is isometric by the
norm lemma above, so also defines a normed `L`-algebra. The extension
henselianity lemma supplies henselianity of `N`. The Galois case embeds
`X(K)` in `X_N(N)`. The map from `X_L(L)` to `X_N(N)`, including the
canonical tower isomorphism, is continuous. Cancelling it with
`IsEmbedding.of_comp` proves the embedding into `X_L(L)`.

For the final theorem set `S = separableClosure K L`. This is a finite
separable extension of `K`, carrying its inherited norm, and
`separableClosure S L = ⊥`. The separable case embeds `X(K)` into
`X_S(S)`. The trivial-relative-separable-closure case embeds the latter
into `(X_S)_L(L)`. The base change of `X` retains quasi-separatedness and
local finite type. Composing with the homeomorphism from `towerIso`
and using `fieldExtensionPointMap_tower` gives precisely the map in the
published target.

No completeness, module topology, separability of `L/K`, separatedness,
or cover by separated open subspaces is added to the target. The theorem
does not assert that its image is closed.
