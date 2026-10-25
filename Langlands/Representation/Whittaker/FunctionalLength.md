# Functional length along actual finite filtrations

This internal adapter measures the full character-equivariant functional space
by its module length over the coefficient field. The value lies in the extended
natural numbers; infinite-dimensional functional spaces have infinite length.
It imposes no implicit finite-dimensionality assumption.

The existing `Langlands.Whittaker.functionalsCongr` from
`RankinSelberg.WhittakerTypeEquivalence` transports the actual functional spaces along an actual
representation equivalence by precomposition with the inverse intertwiner.
`functionalLength` is invariant under this equivalence, vanishes exactly when
the functional space is zero, and is nonzero exactly when `HasFunctional` holds.
An explicit linear equivalence of the functional space with the coefficient
field gives functional length one. The bottom and top invariant subspaces have
length zero and the ambient functional length, respectively.

Over the complex numbers, assume the group is a topological group, the subgroup
is a limit of compact subgroups in the Library's compact-containment sense, and
the scalar values of its character are locally constant.
`functionalLength_eq_add_of_exact` applies `FunctionalExactness` to actual
intertwiners with injective first map, surjective second map, range equal to
kernel, and smooth middle representation. The resulting functional sequence is
contravariant and short exact, using the published `functionalsComap` map
and its exactness lemmas. Mathlib's `Module.length_eq_add_of_exact` gives
additivity, with the two summands reordered.

`functionalLength_filtration_step` applies this result to the actual inclusion
and quotient projection in `ObjectRepFiltration`. Smoothness of each upper step
is inherited from the ambient representation along its injective inclusion.
The range/kernel identity is checked on quotient classes.
`functionalLength_eq_sum_of_filtration` then telescopes these identities by
induction through the finite chain, using its zero and full endpoints.
No simplicity assumption on the graded quotients is needed.

`functionalLength_factors_of_eq_one` proves that if the total functional length
is one, exactly one graded factor has functional length one and every other
factor has length zero. The proof uses the sum formula: a nonzero summand is at
least one and at most the total, and cancellation of that finite summand forces
the sum of the remaining lengths to vanish.
`existsUnique_hasFunctional_factor` expresses the consequence using the actual
nonzero-functional predicate when a linear equivalence with the complex numbers
is supplied for the total functional space. The uniqueness counts positions in
the supplied filtration, so repeated isomorphic factors retain their multiplicity.

The provenance is internal: functional exactness, Mathlib module length, and the
Library's actual object-filtration constructions. The quotient and telescoping
arguments follow the existing `Filtration.RepresentationLength` implementation,
with the additive invariant replaced by the functional-space length.
This module alone supplies neither a finite filtration nor a classification of
its constituents, and does not prove equal-rank trilinear uniqueness.
