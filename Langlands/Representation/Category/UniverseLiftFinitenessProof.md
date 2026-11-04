# Proof of actual finiteness invariance under a universe lift

Worker 1210, in coordination with Worker 189.

`Langlands.universeLiftFiniteness` proves the internal
`Langlands.UniverseLiftFinitenessStatement` with independent universes
`uX`, `uG` and `uV`.

For `SmoothRep.moduleFinite_universeLift_iff`, the published actual
representation equivalence `SmoothRep.universeLiftEquiv.{uX} A` and its
inverse are converted to group-algebra linear maps using
`Representation.IntertwiningMap.equivLinearMapAsModule`. This conversion
keeps their underlying functions, so both resulting maps are surjective.
Each implication installs its finite-generation premise as a local
instance and applies `Module.Finite.of_surjective` to the map in the
required direction. Thus finite generation is over `MonoidAlgebra ℂ G`
on both sides.

`SmoothRep.hasFiniteLength_universeLift_iff` uses the same two maps.
`IsFiniteLength.of_surjective` transfers finite length from the source
module to the target module. Use the inverse equivalence to descend
length from the lift, and the forward equivalence to lift length from
the original representation. These are precisely the actual module
predicates in `SmoothRep.HasFiniteLength`.

The final theorem pairs these two deductions. This is internal
implementation content derived from the published universe-lift
equivalence and Mathlib's module-image results. The existing generic
cross-carrier finite-length transport in
`Langlands.Derivative.hasFiniteLength_iff_of_equiv` is a related stronger
transport result; the present module supplies the direct universe-lift
specializations beside `Category.UniverseLift`, without requiring the
derivative constructions.

No hypothesis relates the group universe to either carrier universe, and
no nonzero hypothesis is used. The proof includes zero representations.
It proves neither reductive structural realizations nor the final Howe
finite-length implication.
