# Signed quotient-curve bounds from pseudo-reductivity

Authors: Worker 1549, Worker 1547, and Worker 317.

This internal construction works over an algebraically closed field in universe
`u`, in every characteristic. It specializes the proved unipotent curve bound
to an actual signed dynamic direction and then transfers the bound to roots
positive for the original cocharacter. It requires no proof of
`AlgClosedReductiveNormalSolvableTorusStatement`.

`signedCurveUnipotentDataOfPseudoReductive` takes a pseudo-reductive ambient
group `G`, a proper solvable closed subgroup `b : B → G`, and a split torus
mapping into `B`. The supplied map `q : G → Q` is quasi-compact, smooth and
surjective, has exact right-coset fibers on every scheme test, and has a
separated target of topological Krull dimension at most one. The dynamic
centralizer of the supplied cocharacter must be contained in the all-test
image of `B`. Smoothness of `B` follows from the exact smooth quotient and
affineness follows from the closed inclusion.

The constructor returns the existing `SignedCurveUnipotentData` structure.
The proved signed noncontainment construction selects a cocharacter equal
to the supplied one or its negative whose dynamic unipotent subgroup is not
contained in `B`. For that same direction,
`curveUnipotentDataOfPseudoReductive` constructs the actual smooth connected
affine unipotent representative with its closed inclusion, moving dominant
quasi-compact quotient-curve orbit, and Lie dimension at most one. Its bound
uses the proved unipotence of the solvable smooth connected normal closure
and triviality of the ambient unipotent radical.

`positive_roots_eq_of_rankOne_curve_quotient_of_isConnectedReductive`
specializes this constructor to a connected reductive group, a split maximal
torus, and actual roots that are pairwise linearly dependent over the
integers. A supplied normalizer point has nonidentity class in the actual
relative Weyl quotient `N(k)/Z(k)`. For the original cocharacter `ν`, the
constructor is applied to its integral normalizer symmetrization
`η = ν - wν`; dynamic centralizer containment is required for this `η`.
The returned data bound one of the two intrinsic signed dynamic tangent
dimensions. The existing signed tangent comparison identifies their
dimensions by actual conjugation and doubles the root pairings integrally.
Its positive-root bound then gives equality of any two actual roots with
strictly positive pairing against the original `ν`. This argument uses no
division by two and imposes no characteristic restriction.

The provenance is internal. Worker 1547 implemented the existing signed curve
assembly in `Reductive.RankOneCurvePositiveRoots`; Worker 1549 adapts it using
the proved pseudo-reductive unipotent curve constructor and the earlier signed
tangent bridge. Worker 317 contributed the normality and action-kernel route
used by the unipotent curve bound. This pair reuses those actual constructions
and their stated hypotheses.

Existence of the proper solvable closed subgroup and its quotient, the
quotient's curve dimension, symmetrized-centralizer containment, pairwise
integral root dependence, and the nonidentity normalizer class remain
supplied. The unrestricted `RankOnePositiveRootUniquenessStatement` remains
a separate proof obligation.
