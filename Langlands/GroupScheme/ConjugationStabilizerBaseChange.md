# Conjugation stabilizers under base change

For a morphism from a relative scheme into a group scheme, its conjugation stabilizer consists of points for which conjugation and inverse conjugation preserve all points factoring through the morphism, on every refinement of the given test. If the relative scheme and its morphism into the group are pulled back to a new base, then this subgroup functor is the base change of the original stabilizer.

The pullback square identifies factoring points under the pullback adjunction. The resulting point equivalence is multiplicative and respects restriction. Conversely, every refinement of a test viewed over the original base has a structure morphism to the new base through that test. It therefore occurs, up to an isomorphism of tests, among the refinements over the new base. This gives both directions of the equality on all tests.

The statement is an internal extension of `SubgroupFunctor.normalizer_baseChange` to the stabilizer of a relative subscheme, such as an actual identity jet.
