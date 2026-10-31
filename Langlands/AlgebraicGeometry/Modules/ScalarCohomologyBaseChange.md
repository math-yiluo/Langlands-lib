# Scalar-linear cohomology base-change maps

This internal construction linearizes the published `baseChangeMap` from
`CohomologyBaseChange`. For a commutative square `g ≫ f = f' ≫ Spec.map φ`,
it takes a module `M` such that the positive higher direct images of `g^* M`
along `g` vanish. For each nonnegative degree `n`, `scalarBaseChangeMap` is
the `R'`-linear map

`R' ⊗[R] Hⁿ_R(X, M) → Hⁿ_{R'}(X', g^* M)`

corresponding under Mathlib's extension/restriction scalar adjunction to the
published semilinear base-change map. Its definition uses the published
`pushforwardInjectiveAcyclic` proof to discharge the other acyclicity hypothesis
of `baseChangeMap`; no new injective-acyclicity assumption is imposed.

The `homEquiv` lemma identifies its adjunct with `baseChangeMap` for any proof
of the latter's injective-acyclicity condition. The `unit` lemma gives the same
identity as a composition with the scalar unit. The `one_tmul` lemma says that
`1 ⊗ x` maps to the semilinear base-change image of `x`. Coefficient naturality
follows by injectivity of the scalar adjunction's Hom equivalence, its two
naturality identities, and the published `baseChangeMap_naturality`.

The module retains arbitrary universe `u`. It assumes neither a cartesian
square, flatness, nor quasi-coherence. It constructs a specified map and
proves its compatibility formulas; it asserts no base-change isomorphism,
localization theorem, perfection, section lifting, or relative cube theorem.
Its provenance is the cited published Library constructions and Mathlib's
scalar adjunction, with no new external mathematical assertion.
