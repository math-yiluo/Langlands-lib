# Normalized induction across carrier universes

This internal carrier-transport construction is derived from the existing
full-parabolic normalized induction functor, the published scalar-twist and
smooth-induction equivalences, and the existing universe lift. It provides no
finite-length proof for an induced irreducible representation.

For any locally compact nonarchimedean group, actual semidirect decomposition
`P = M ⋉ U`, and proof that `U` is closed, an actual complex representation
equivalence between smooth Levi representations induces
`normalizedInductionEquivOfEquiv`. Its source and target carriers may lie in
independent universes `uV` and `uW`. The output carriers have universes
`max uG uV` and `max uG uW`. This is `Representation.Equiv`, rather than an
isomorphism between objects of different fixed-universe categories.

The construction first inflates the original linear equivalence along the
actual projection. It then applies the same full-parabolic half-character
twist on both sides and applies `Induction.smoothInducedEquiv`. The displayed
evaluation theorem states that the forward map applies the original
equivalence to every function value. Its inverse applies the inverse
equivalence pointwise. Thus covariance, smoothness and equivariance are supplied
by the existing proved smooth-induction construction, with no additional
projection-continuity or normalization-comparison premise.

`normalizedInduction_hasFiniteLength_iff_of_equiv` converts the equivalence and
its inverse into surjective linear maps over the actual ambient complex group
algebra. The existing `IsFiniteLength.of_surjective` transfers finite length
in both directions, including across the independent carrier universes.

`normalizedInductionUniverseLiftEquiv` applies this construction to
`SmoothRep.universeLiftEquiv`. Its pointwise maps are respectively `ULift.up`
and `ULift.down`. The final iff theorem shows that induction of a universe
lift has finite length exactly when induction of the original representation
does. Lifting the inducing carrier from `uV` to `max uV uX` therefore does not
restrict the inducing representation. These are transport results only; they
assume neither irreducibility nor finite length, and establish no new
representation-theoretic finiteness assertion. They can transport a separately
proved result with a larger carrier convention to the exact independent
universe scope of `DynamicInductionIrreducibleFiniteLengthStatement`.
