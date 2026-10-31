# The natural quotient onto an inner product-Levi composite

This internal development constructs natural comparisons on the full smooth
representation category, using the published normalized induction in stages,
function-preserving composed/flattened induction comparison, and Jacquet
evaluation at the identity. There are no finite-length or admissibility
assumptions.

The function-preserving objectwise comparisons commute with all coefficient
maps because those maps act by pointwise postcomposition. They therefore
assemble into `composedFlattenedInductionIso`. Pullback along the flattened
Levi equivalence and its inverse cancels by the identity linear map.
Combining these two comparisons with the published natural induction in
stages gives `flattenedInductionInStagesIso`.

This is internal infrastructure derived from the named published
constructions. `flattenedJacquetNaturalMap` assembles the published
`Parabolic.flattenedJacquetQuotientMap` into a natural map from the Jacquet
quotient for the flattened target shape to the iterated coarse and refined
Jacquet quotients. Naturality follows by lifting a vector to a representative
and observing that both routes postcompose that representative by the same
coefficient map. `parabolicJacquetEvaluation` assembles evaluation at the
identity into a natural map from normalized induction followed by normalized
Jacquet to the identity functor.

The main definition, `productLeviQuotientMap`, composes the induction-in-stages
isomorphism, the flattened Jacquet quotient, and refined Jacquet applied to
the coarse evaluation map. Its source is the actual ambient
`jacquetInductionFunctor T (B.flatten Q) (B.flatten S)`, and its target is the
actual `innerJacquetInductionFunctor T B Q S`. In particular, the normalization
is inherited from the published constructions, including their positive
half modulus for induction and inverse half modulus for Jacquet.

`productLeviQuotientMap_surjective` proves surjectivity of every component.
Given an inner Jacquet class, first choose a vector representing it. The
published `CuspidalSupport.normalizedParabolicInduced_eval_surjective`
provides a smooth induced function taking this vector as its value at the
identity. Transport this function back through induction in stages and take
its flattened Jacquet class. The constructed comparison sends that class to
the original inner class. This argument uses only smoothness and works with
independent field and coefficient universes.

This file does not identify the kernel with an open support step or assert a
support-filtration comparison. Those remain additional geometric obligations;
the product-Levi geometric lemma itself is not proved here.
