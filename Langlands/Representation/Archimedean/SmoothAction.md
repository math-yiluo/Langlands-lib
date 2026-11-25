# Group action and dense continuous extensions in the derivative topology

This internal prerequisite to the proof of
`CuspidalOperatorMultiplicityOneStatement` builds on the published module `SmoothDerivativeTopology`. It
acts by each fixed group element on the dedicated copy
`DerivativeSmoothVectors` of the smooth vectors, which carries the genuine
word-derivative topology. It also proves uniqueness and covariance of
continuous scalar functionals on a supplied image that is dense in that
topology. All declarations are in the namespace
`Langlands.Archimedean.SmoothAction`.

## Setting and retained hypotheses

The setting is that of the published `SmoothVectors`, `SmoothDerivative` and
`SmoothDerivativeTopology` modules. `𝔤` is a real normed space, the model
vector space. `I : ModelWithCorners ℝ 𝔤 H` is a model with corners on the
model manifold `H`. `G` is a group with a topology, charted on `H`, and
`[LieGroup I ∞ G]` makes it a smooth real Lie group. `E` is a complex normed
space, and the representation `π : G →* (E →L[ℂ] E)` is supplied: a
homomorphism into the bounded complex operators. These four types have the
independent free universes `u𝔤`, `uH`, `uG` and `uE`. The dense-extension
section adds a complex module `V` in a fifth free universe `uV`. No
completeness of `E` and no joint continuity of `π` is assumed. The tangent
space of `G` at the identity is the model space `𝔤`; Mathlib computes
manifold derivatives at the identity in the chart at the identity.

## Conjugated directions and the chain rule

`conjugateDirection I g : 𝔤 →L[ℝ] 𝔤` is
`mfderiv I I (fun h => g⁻¹ * h * g) 1`. This is the real tangent map at the
identity of conjugation `h ↦ g⁻¹ h g` by the inverse of `g`, in the chart at
the identity. Conjugation fixes the identity, so this is a linear map of `𝔤`
to itself.

`lieDerivative_apply` states, for `g : G`, `X : 𝔤` and a smooth vector `v`,

`lieDerivative I π X (π g v) = π g (lieDerivative I π (conjugateDirection I g X) v)`.

Thus `dπ(X)(π(g)v) = π(g) dπ(Ad(g⁻¹)X) v` in conventional notation. The
proof writes `c h = g⁻¹ * h * g` and `A` for `π g` restricted to real
scalars. The orbit map of `π g v` is `h ↦ π h (π g v) = π (g * c h) v`,
so it equals `A ∘ (orbitMap π v ∘ c)`. The map `c` is smooth because
multiplication in the Lie group is smooth, and `c 1 = 1`. The orbit map of
`v` is differentiable at `1` because `v` is a smooth vector. The real
manifold chain rule `mfderiv_comp` is applied twice: once to `A` after the
composite, and once to the orbit map after `c`. The derivative of the
bounded linear map `A` is `A` itself (`ContinuousLinearMap.mfderiv_eq`).
Evaluating the composite derivative at `X` gives the displayed identity.

`iteratedLieDerivative_apply` extends this to every genuine word: for
`Xs : List 𝔤` and a smooth vector `v`,

`iteratedLieDerivative I π Xs (π g v) =
  π g (iteratedLieDerivative I π (Xs.map (conjugateDirection I g)) v)`.

The word convention is the published one,
`[X₁,…,Xₖ] ↦ dπ(X₁) ⋯ dπ(Xₖ)`, and every letter is transformed by the
same tangent map. The proof is induction on the word. The empty word is
trivial. For `X :: Xs`, the induction hypothesis rewrites the inner word and
`lieDerivative_apply` handles the outer letter. Its smoothness hypothesis
holds because the transformed word applied to `v` is a smooth vector, by
the published `smoothIteratedLieDerivative`.

`wordSeminorm_apply_le` states, for every word `Xs` and every smooth vector
`v`,

`wordSeminorm I π Xs (smoothRepresentation I π g v) ≤
  ‖π g‖ * wordSeminorm I π (Xs.map (conjugateDirection I g)) v`.

It rewrites both seminorms as norms of word derivatives, applies the word
formula, and uses the operator-norm bound of `π g`.

## The fixed-element action on the derivative topology

`derivativeActionLinear I π g` is the complex-linear map on
`DerivativeSmoothVectors I π` obtained by conjugating the published
`smoothRepresentation I π g` with the linear equivalence
`DerivativeSmoothVectors.toSmooth`. Its simp lemma
`toSmooth_derivativeActionLinear` holds by definition.
`derivativeCoordinates_derivativeActionLinear` states that the `Xs`
coordinate of the translated vector is
`π g` applied to the `Xs.map (conjugateDirection I g)` coordinate of the
original vector. It is the word formula read through the published
coordinate evaluation `derivativeCoordinates_apply`.

`continuous_derivativeActionLinear` proves continuity in the derivative
topology. That topology is induced by the coordinate map
`derivativeCoordinates` into the product `List 𝔤 → E`. By the universal
property of the induced topology (`continuous_induced_rng`), it suffices that
the composite into the product is continuous. By the universal property of
the product topology (`continuous_pi`), it suffices that each coordinate
`Xs` of the translated vector is continuous. That coordinate equals the
published continuous projection
`derivativeCLM I π (Xs.map (conjugateDirection I g))` followed by the
bounded operator `π g`, so it is continuous.

`derivativeAction I π g` bundles this map as a continuous complex-linear
operator. `toSmooth_derivativeAction` records its agreement with the
published smooth action after forgetting the topology.
`derivativeCoordinates_derivativeAction` gives its coordinate formula,

`derivativeCoordinates I π (derivativeAction I π g v) Xs =
  π g (derivativeCoordinates I π v (Xs.map (conjugateDirection I g)))`.

`derivativeRepresentation I π` packages these operators as a monoid
homomorphism
`G →* (DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors I π)`.
The identity and multiplication laws follow from injectivity of `toSmooth`
and from the corresponding laws of the published `smoothRepresentation`.
`derivativeRepresentation_apply` identifies its value at `g` with
`derivativeAction I π g`. `toSmooth_derivativeRepresentation` states agreement
with `smoothRepresentation I π g`. Only continuity of each fixed operator
is asserted. Neither joint continuity on `G × DerivativeSmoothVectors I π`
nor continuity in `g` is asserted.

`isContinuousOnSmoothVectors_comp` proves: if a complex-linear functional
`L` on `smoothVectors I π` satisfies `IsContinuousOnSmoothVectors I π L`,
then so does `L.comp (smoothRepresentation I π g)`. The published bridge
`continuous_of_isContinuousOnSmoothVectors` makes `L` continuous on the
dedicated copy. Composition with the continuous operator
`derivativeAction I π g` is continuous. The published converse
`isContinuousOnSmoothVectors_of_continuous` returns the finite-word bound.

## Dense continuous extensions

In this section `V` is any complex module, in its own universe, and
`j : V →ₗ[ℂ] smoothVectors I π` is any complex-linear map.
`derivativeEmbedding I π j : V →ₗ[ℂ] DerivativeSmoothVectors I π` is
`j` followed by the inverse of `toSmooth`. Its simp lemma
`toSmooth_derivativeEmbedding` recovers `j v`. The map `j` need not be
injective.

Both results below take the explicit hypothesis
`hd : DenseRange (derivativeEmbedding I π j)`. It states density of the
image in the genuine derivative topology, that is, simultaneously in every
genuine word-derivative coordinate. Hilbert or Banach norm density of the
image in `E` is not substituted for this hypothesis.

`eq_of_agree_on_dense_embedding` takes two complex-linear functionals
`L₀ L₁` on `smoothVectors I π`, both satisfying
`IsContinuousOnSmoothVectors`, with `L₀ (j v) = L₁ (j v)` for every `v : V`.
It concludes `L₀ = L₁`. The published bridge makes the two transported
functionals continuous on the dedicated copy, and they agree on the dense
range. Mathlib's `DenseRange.equalizer`, valued in the Hausdorff space `ℂ`,
makes them equal. Evaluating at the inverse of `toSmooth` gives equality on
every smooth vector.

`isWhittakerFunctional_of_dense_embedding` takes an arbitrary subgroup
`N : Subgroup G`, an arbitrary homomorphism `χ : N →* ℂˣ`, and a
complex-linear functional `L` with `IsContinuousOnSmoothVectors I π L`. Its
covariance hypothesis is required only on the image:

`L (smoothRepresentation I π (u : G) (j v)) = (χ u : ℂ) * L (j v)` for all
`u : N` and `v : V`.

It concludes `IsWhittakerFunctional I π N χ L`. The continuity component is
the hypothesis on `L`. For the covariance component, fix `u`. The function
`w ↦ L (toSmooth (derivativeAction I π u w))` is continuous because the fixed
element acts continuously. The function `w ↦ (χ u : ℂ) * L (toSmooth w)` is
continuous because scalar multiplication is continuous. The hypothesis says
that the two functions agree on the dense range, so `DenseRange.equalizer`
makes them equal. Evaluating at the inverse of `toSmooth` gives covariance
on every smooth vector.

## Provenance and scope

This is internal derived infrastructure. It composes the published
smooth-vector, genuine-derivative and derivative-topology constructions with
Mathlib's real manifold chain rule, the universal properties of induced and
product topologies, and the dense equalizer theorem. No external literature
result is translated directly; the Whittaker predicate is the published
`IsWhittakerFunctional`.

The supplied representation `π` and the derivative-topology density
hypothesis `hd` remain explicit. The module does not construct a cuspidal
or other actual globalization. It does not prove that any particular image is
dense in the derivative topology, and it does not prove joint continuity of
the action. No multiplicity-one theorem is proved here.
