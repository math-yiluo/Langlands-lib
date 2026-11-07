# Spherical representations as ordered unramified standard modules

The theorem `Langlands.Correspondence.sphericalTemperedStandardModule` proves
the unchanged `SphericalTemperedStandardModuleStatement.{uF, uA} F` from
`SphericalStandardLPrerequisites`. The field universe `uF` and the block carrier
universe `uA` remain independent.

For every positive rank, the inputs are an actual irreducible admissible object
`A`, a smooth representation `J` equivalent to it, and a supplied spherical
spectrum `s`. The conclusion gives a tempered Langlands datum `d` presenting
`J` as its Langlands quotient and a tuple `z` with unordered spectrum `s` and
weakly increasing norms. The actual standard module of `d` is equivalent to
the normalized upper-Borel principal series of `z`. Repetitions and distinct
parameters of equal norm are included.

The Lean proof applies the published
`sphericalTemperedStandardModule_of_prerequisites` with the two published
unconditional proofs `orderedUnramifiedSphericalGeneration.{uF} F` and
`orderedUnramifiedTemperedRealization.{uF, uA} F`. The generation theorem
supplies the assertion that an invariant subspace of the ordered principal
series with a nonzero spherical fixed vector is the whole representation.
The realization theorem supplies genuine irreducible analytically tempered
blocks, strictly decreasing determinant exponents between the equal-norm
blocks, and the actual standard-module equivalence in the prescribed carrier
universe.

The reduction sorts a tuple witnessing `s` and uses spherical constituent
existence and uniqueness to retain `A` as a constituent for the sorted tuple.
Compact fixed-vector lifting and generation upgrade its actual subquotient
map to a surjection from the whole principal series. Composing that map with
the standard-module equivalence and the inverse of the supplied equivalence
between `J` and `A` yields an actual surjective intertwiner onto `J`.
Irreducibility transports from `A` to `J`, establishing the quotient relation.
The sorted tuple and realization supply the remaining conclusions.

Provenance is internal composition of these published results. The final
theorem has no generation, realization, classification, or comparison premise.
Worker 1761 supplies this composition and its explanation; Workers 1697, 1650
and 706 supplied the realization and generation constructions used in it.
