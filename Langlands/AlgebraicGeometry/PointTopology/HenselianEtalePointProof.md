# Proof of the henselian assertions on Conrad's printed p.14

`henselianEtalePoint` proves `HenselianEtalePointStatement`. The first conjunct
is `henselianSeparablyClosedInCompletion` and the second is
`henselianEtalePointLocalHomeomorph`, Conrad's Lemma 5.3. Throughout, `K` is a
nontrivially normed field, `K̂` is `UniformSpace.Completion K` with its
completion norm, and both point spaces carry `schemePointTopology`.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.14: the henselian characterization and Lemma 5.3. It is
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Worker 105 authored the shared proof draft; Worker 1607 checked and prepared
this proof for independent review. The coefficient embedding, fibre rationality
and local injectivity lemmas below are internal supporting results for this
proof; their constructions are described here.

The route follows Conrad's proof of Lemma 5.3. The étale map is open on
`K̂`-points because `K̂` is complete. Separable closedness of `K` in `K̂` shows
that a `K̂`-point lying over a `K`-point is itself a `K`-point. Local
injectivity comes from the open diagonal of an unramified morphism.

## Separable closedness in the completion

`separableClosure_completion_eq_bot` takes `x ∈ K̂` separable over `K` and
assumes that `x ∉ K`. Then the minimal polynomial of `x` has degree at least
`2`. Being separable, it has two distinct roots `r₁ ≠ r₂` in
`AlgebraicClosure K`. Let `L = K⟮x⟯`, a finite extension of `K`. The two roots
give `K`-embeddings `σ₁, σ₂ : L → AlgebraicClosure K` with `σᵢ x = rᵢ`
(`IntermediateField.algHomAdjoinIntegralEquiv`).

The henselian hypothesis is applied twice. Applied to `AlgebraicClosure K`, it
gives an absolute value `w` extending the norm of `K`. Applied to `L`, it gives
uniqueness. Let `v₀` be the restriction of the completion norm to `L ⊆ K̂`, and
pull `w` back along `σ₁` and along `σ₂`. All three are absolute values on `L`
extending the norm of `K`, so they coincide. Since `K` is dense in `K̂`, for
every `ε > 0` there is some `k ∈ K` with `v₀ (x - k) < ε`. Then

`w (r₁ - r₂) ≤ w (σ₁ x - k) + w (k - σ₂ x) = v₀ (x - k) + v₀ (k - x) < 2ε`.

Taking `ε = w (r₁ - r₂) / 4` forces `w (r₁ - r₂) = 0`, so `r₁ = r₂`. This
contradicts the choice of distinct roots. Only the existence and uniqueness of
extensions in `IsHenselianValuedField` are used. Neither completeness nor an
ultrametric inequality is assumed.

## Coefficient embedding for arbitrary schemes

`isEmbedding_schemeChangeRing` holds for any relative scheme `X` over `Spec R`.
Let `S` and `T` be local topological `R`-algebras, with `T` having continuous
multiplication and open units. Let `f : S → T` be a local `R`-algebra map that
is a topological embedding. Then `RingPoint.changeRing f` is a topological
embedding from `S`-points to `T`-points. The affine case is the published
`affineSchemeCoefficientEmbeddings_proof`, applied to every affine open chart.
The global statement is assembled as follows.

- `changeRing_left_closedPoint`: because `f` is local, the image of the closed
  point does not change under change of coefficients. So a `T`-point coming
  from an `S`-point `p` factors through an open `U` exactly when `p` does
  (`range_subset_open_iff_closedPoint`, `openPointLift`).
- Injectivity: choose an affine chart through which `p` factors, using
  `exists_affineOpenPoint`. Lift the other point to the same chart. Then apply
  chart injectivity together with `openPointMap_injective`.
- Inducing: continuity is `schemeCoefficientContinuity_proof`. Conversely, let
  `W` be open. On each affine chart, the preimage of `W` is pulled back from an
  open set `t U` of `T`-points. Push each `t U` forward by the open chart
  embedding `isOpenEmbedding_schemeAffineChart`, and take the union. Its
  preimage is `W`.

## Fibre rationality

`exists_lift_of_formallyUnramified` treats a morphism `f : X → Y` that is
formally unramified and locally of finite type, and a field extension `k ⊆ L`
with `separableClosure k L = ⊥`. Let `q` be an `L`-point of `X` whose image is
the base change of a `k`-point of `Y`. Then `q` is the base change of a
`k`-point of `X`.

The proof works through `Scheme.SpecToEquivOfField`. The point `q` corresponds
to a point `x` of `X` and an embedding `φ` of the residue field `κ(x)` into
`L`. The `k`-point of `Y` corresponds to the point `f x` and an embedding of
`κ(f x)` into `k`. These are compatible with `φ`. Mathlib's instance for
formally unramified locally finite type morphisms makes `κ(x)` separable over
`κ(f x)`. So every `φ z` is a root of a separable polynomial with coefficients
in `k`: the image of the minimal polynomial of `z`. It is therefore separable
over `k`, and it lies in `k` because `separableClosure k L = ⊥`. This factors
`φ` through `k` and gives the `k`-point. The relative form
`exists_changeRing_eq_of_formallyUnramified` also checks that the lift lies
over `Spec k`, because `Spec.map` is injective on field maps.

## Local injectivity

`isLocallyInjective_schemePointMap` holds over any topological local ring `S`
with open units. Let `f` be formally unramified and locally of finite type.
Then postcomposition with `f` is locally injective on `S`-points. The diagonal
of `f.left` is an open immersion (Mathlib's
`FormallyUnramified.isOpenImmersion_diagonal` instance). It therefore gives an
open embedding on points (`isOpenEmbedding_schemePointMap`). The homeomorphism
`schemePullbackPointHomeomorph` identifies points of the fibre product with
pairs of points that agree in `Y`. Under it, the range of the diagonal is
exactly `Function.pullbackDiagonal` of the point map. That set is therefore
open, which is `isLocallyInjective_iff_isOpen_diagonal`.

## Assembly

- `isOpenMap_completionSmoothPointMap`: for a smooth `f` over `K`, the map on
  `K̂`-points is open. Base change along `K → K̂` gives a smooth morphism over
  `K̂` (`MorphismProperty.overPullbackMap`). The published
  `isOpenMap_smoothSchemePointMap` applies to `K̂`, regarded as a nontrivially
  normed complete field (`completionNontriviallyNormedField`). The
  homeomorphisms `schemeBaseChangeTopology_proof` and the naturality
  `ringPointBaseChangeEquiv_natural` transport openness back.
- `isOpenMap_henselianEtalePointMap`: let `W` be open in `X(K)`. It is the
  preimage of an open set `Ŵ ⊆ X(K̂)`, because `X(K) → X(K̂)` is an embedding.
  This uses `isEmbedding_schemeChangeRing` with the uniform embedding
  `K → K̂`. The image `f(W)` equals the preimage in `Y(K)` of the open set
  `f(Ŵ)`. One inclusion is associativity of composition. The other uses fibre
  rationality, with `separableClosure_completion_eq_bot`, and injectivity of
  `Y(K) → Y(K̂)`.
- `henselianEtalePointLocalHomeomorph`: the point map is continuous
  (`schemePointContinuity_proof`), open and locally injective. Its restriction
  to an open set on which it is injective is therefore an open embedding. This
  is the criterion `isLocalHomeomorph_iff_isOpenEmbedding_restrict`.

The proof does not use the hypotheses that `X` and `Y` are locally of finite
type over `K`. It needs only that `f` is étale, which makes `f` smooth,
formally unramified and locally of finite type.
