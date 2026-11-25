# Genuine derivatives of smooth vectors

This internal prerequisite to the proof of `CuspidalOperatorMultiplicityOneStatement` proves that
the genuine orbit derivatives defined in
`Langlands.Representation.Archimedean.SmoothVectors` preserve smooth vectors
and are complex linear there. It bundles their words as linear maps and
their norms as complex seminorms. Its companion
`SmoothDerivativeTopology` uses these maps to define a topology and extend
functionals satisfying finite word bounds.

## Setting and definitions

All declarations are in `Langlands.Archimedean` and retain independent
universes for the real normed model space `𝔤`, its chart model `H`, the
group `G`, and the complex normed space `E`. Fix a model with corners
`I : ModelWithCorners ℝ 𝔤 H` and a homomorphism
`π : G →* (E →L[ℂ] E)`. The group has a topology and a charted-space
structure. Smooth vectors and derivatives are exactly the published ones:
`IsSmoothVector I π v` says that `g ↦ π(g)v` is real smooth, and
`lieDerivative I π X v` is its manifold derivative at `1` applied to
`X : 𝔤`. No replacement derived action is supplied as data.

The first three lemmas need no Lie-group hypothesis:

- `apply_lieDerivative` identifies
  `π(g)(lieDerivative I π X v)` with the derivative at `h = 1` of
  `h ↦ π(g h)v`, provided `v` is smooth.
- `lieDerivative_add` proves additivity on two smooth vectors.
- `lieDerivative_smul` proves complex homogeneity on a smooth vector,
  even though the orbit derivative is taken over the real numbers.

The remaining declarations assume `[LieGroup I ∞ G]`.
`isSmoothVector_lieDerivative` proves that each genuine derivative of a
smooth vector is smooth. Consequently
`smoothLieDerivative I π X` is a complex-linear endomorphism of
`smoothVectors I π`.

`smoothIteratedLieDerivative I π Xs` composes these endomorphisms for a
list `Xs` of real tangent directions. The empty list is the identity,
and `[X₁, …, Xₖ]` acts by `dπ(X₁) ⋯ dπ(Xₖ)`. Its application lemma
identifies the underlying vector with the existing
`iteratedLieDerivative I π Xs`. Concatenation composes the two word maps
in that order, as stated by `smoothIteratedLieDerivative_append`.

`wordSeminorm I π Xs` is the norm seminorm of `E` composed with this
linear word map and the inclusion into `E`. Its evaluation theorem is
exactly
`wordSeminorm I π Xs v = ‖iteratedLieDerivative I π Xs v‖`.

## Implemented proof

The bounded-operator identity uses the homomorphism law to write the
translated orbit as a composite with `π(g)`, restricted to real scalars.
Mathlib's manifold chain rule and the derivative formula for a continuous
linear map give the equality. Additivity uses `mfderiv_add`, with
differentiability supplied by smoothness. Complex homogeneity uses the
same chain rule with the real restriction of the complex-linear map
`c • id`.

For preservation of smoothness, the map
`(g,h) ↦ π(g h)v` is smooth by smooth multiplication and the smooth orbit
map of `v`. Mathlib's `ContMDiffAt.mfderiv_apply` gives smooth dependence
on `g` of the derivative in the second variable at `h = 1`, evaluated
at the fixed direction `X`. The source tangent chart is constantly
based at `1` and the target is a model vector space, so their coordinate
changes reduce to identities. The bounded-operator identity then
identifies this smooth function with the orbit map of `dπ(X)v`.
Bundling linear maps uses these three lemmas; the word and concatenation
identities follow by list induction. The seminorm construction is the
pullback of the norm seminorm by a complex-linear map.

## Provenance and scope

This is internal derived analysis rather than a transcription of a
literature theorem. Its inputs are the published smooth-vector
definitions and Mathlib's manifold differentiation and seminorm APIs.
In particular it proves the preservation fact described, but not proved,
in point 6 of the published `SmoothVectors.md` discussion of derived
choices.

There is no completeness, joint continuity of the action, admissibility,
irreducibility, finite-dimensionality of `𝔤`, or Hilbert-space hypothesis.
The module constructs neither a representation globalization nor a
density theorem, and proves no Lie-bracket identity or Whittaker
uniqueness result.
