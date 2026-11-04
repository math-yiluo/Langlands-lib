# Natural actual cokernels under exact smooth functors

Worker 1300. Internal module-quotient construction for the associated-Levi
comparison task. This file is an internal prerequisite, not a proof of the
associated-Levi comparison.

For an arbitrary source category and smooth complex representation functors,
`SmoothNatCokernel.functor` takes the actual quotient of the target module by
the invariant range of each component of a natural transformation. Its maps
are the induced module quotient maps. `projection` is the actual natural
quotient projection.

`RepSubfunctor.ambientFirstIso` reuses
`RepSubfunctor.quotientNatIsoOfSurjective` with the full upper subfunctor and
`ExactSmoothTransport.liftNatIso`. Thus a natural surjection whose kernel is
the specified invariant subfunctor identifies that actual quotient naturally.
`ambientFirstIso_projection` specifies this comparison on representatives.

`ExactSmoothTransport.map_range_eq_ker` factors an arbitrary incoming map
through its actual smooth image. The factor onto that image is surjective;
`Derivative.LevelCalculus.map_surjective_of_exact` preserves its surjectivity.
The supplied `MapsShortExactIntertwiners` premise applies to the inclusion of
the image and the given quotient map. Combining the two facts proves middle
exactness after the functor without requiring the incoming map to be injective.
`cokernelIso` then applies the natural first isomorphism theorem to the mapped
presentation. Its projection law sends the actual quotient class of a vector
to the mapped original projection of that vector.

The group, representation carrier, source objects, and source morphisms retain
their independent universes. There are no finite-length, admissibility,
finite-generation, or support assumptions. Exactness is the explicit premise
on the supplied functor; no unproved statement is used as evidence.
The provenance is elementary module quotient algebra and functoriality, using
the published subrepresentation smoothness transfer, natural quotient descent,
and generic short-exactness laws.

The full upper subfunctor is the existing generic `RepSubfunctor.full` from
`Filtration.OneStep`, applied to `F ⋙ SmoothRep.toRep`. No separate specialized
definition is introduced.
