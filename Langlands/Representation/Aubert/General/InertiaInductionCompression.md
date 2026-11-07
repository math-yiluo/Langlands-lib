# Compact compression on normalized inductions of actual inertia blocks

Worker 1751. This internal specialization composes the actual inertia-block
generator-compression bridge with the published normalized induction functor.

`rationalInertiaInductionFunctor L h hU e` first pulls smooth actions of the
rational points of `L` back along the supplied continuous group equivalence
`e` from an actual Levi subgroup. It then applies actual normalized induction
for the supplied semidirect parabolic decomposition. The pullback keeps the
carrier and all linear maps. Its additivity is immediate on those maps.
Mapping an exact row to the underlying modules and using the same maps proves
that pullback retains right exactness; the pinned exact-functor equivalence
therefore gives finite-colimit preservation.

The published normalized-induction results give additivity and finite-colimit
preservation under Hausdorffness, compact-open cofinality, closedness of the
parabolic and continuity of its Levi projection. Compactness of the actual
left quotient gives preservation of the required coproducts. Smooth pullback
already preserves coproducts of the carrier size. The composite therefore
satisfies the actual inertia-block generator-compression hypotheses.

`rationalInertiaInduction_stablePower_of_normKernel` assumes the exact existing
small-progenerator predicate and a stable compression power on the normalized
induction of that actual generator. It transfers precisely the same exponent
to the induced image of every object of the actual lifted inertia block.
`rationalInertiaInduction_stationary_of_normKernel` starts with eventual
stability on the induced generator and gives one positive threshold before
every block object, including both stationary chains and complementarity.

The field, representation carrier and ambient group universes are independent.
The block has carrier universe `max uF uV`; actual induced carriers have
universe `max uG (max uF uV)`. There is no representation admissibility,
finite-dimensionality, finite-type or finite-length hypothesis.
The geometric, small-progenerator and generator-image stability conditions
remain explicit. This module does not prove them, construct a whole-category
inertia decomposition, or prove the dynamic-parabolic stabilization endpoint.
