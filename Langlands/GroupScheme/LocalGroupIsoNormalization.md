# Representation-free normalization and adjoint orbit coordinates

Let `G,H` be group schemes over any scheme `S`. An
`ActualNormalization (G := G) (H := H)` gives a natural normalization of
actual isomorphisms after every base change, invariant under fppf-local
inner equivalence and preserving that equivalence class.

`ActualNormalization.localNormalize` transports this operation to
`LocalGroupIso G H T`, using the equivalence between natural all-test
families and actual isomorphisms of the groups pulled back to `T`.
Its definition and the normalization results in this namespace require no
scheme representing isomorphisms. `localNormalize_refine` proves
naturality for every morphism of relative tests.
`localNormalize_idempotent` follows from invariance and preservation of
the inner class.

## Full-centre adjoint correction

Suppose `q : G → A` is a supplied `IsRelativeAdjointQuotient`.
`localNormalize_invariant` says that inverse precomposition of a family
by the inner action of any `A(T)` point preserves its normalization.
Indeed the resulting actual automorphism is fppf-locally inner, because
the acting point locally lifts through the full-centre quotient. The
proof uses this local lifting theorem and never chooses a global lift
of the adjoint point to `G`.

`localNormalize_decomposition` proves that, for each relative test `T`
and family `e`, there is a unique point `d : T → A` satisfying

`(localNormalize T e).twist hq.innerAction d⁻¹ = e`.

The existing full-centre quotient theorem gives the unique adjoint
representative of the actual discrepancy between `e` and its
normalization. The base-change point equivalence puts this representative
on `T` itself, and its inverse gives the convention of inverse
precomposition in the displayed equation. The actual/local-family
equivalence transfers both the equation and uniqueness.

## From normalized labels to an orbit bijection

For an arbitrary parameter scheme `U` and family
`E : LocalGroupIso G H U`, `localOrbit_bijective` assumes two precise
classification inputs:

- Each refinement `E.refine b` is normalization-fixed, on every test.
- For every test `T` and family `e` over `T`, there is a unique morphism
  `b : T → U` for which `E.refine b` is the normalization of `e`.

It then proves that `(d,b) ↦ (E.refine b).twist hq.innerAction d⁻¹`
is bijective onto all `LocalGroupIso G H T` on every test `T`.
Normalization detects the parameter coordinate in the injectivity proof;
the preceding unique adjoint correction detects the acting coordinate.
The same two existence results prove surjectivity.

`GroupIsomorphismScheme.orbit_bijective_of_local` separately transports
any such representation-free orbit bijection into any supplied
`GroupIsomorphismScheme I`. Its section is `I.classify E`. Evaluation of
the universal family identifies the represented action with the local
twist, and the classifying bijection transfers bijectivity. Thus this
last theorem accommodates arbitrary supplied representers.

There are no affineness, connectedness, reducedness, or nonemptiness
assumptions on the test schemes. The normalized-label classification
premises remain explicit: this module does not prove the pinned
constant-label classification.

## Provenance

This internal construction is derived from the existing actual
normalization and full-centre adjoint discrepancy interfaces. Its
implemented argument is the representation-free version of the existing
represented-point normalization proof in
`OuterIsomorphismActualNormalization`, followed by an abstract orbit
bijection criterion. It supplies infrastructure for the pinned
constant outer-isomorphism chart and for constructing an actual
self-automorphism representer without circularity.
