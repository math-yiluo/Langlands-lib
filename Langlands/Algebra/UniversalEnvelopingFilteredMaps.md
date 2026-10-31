# Maps of the enveloping degree filtration

This is an internal consequence of the published
`Langlands.Algebra.UniversalEnvelopingFiltration`. For any commutative ring
and two Lie algebras over it, an algebra homomorphism between their actual
universal enveloping algebras preserves every degree piece if it maps each
canonical Lie generator into degree one.

`algHom_mem_degreeOne` decomposes an element into a scalar and an element
of the range of the canonical generator. Algebra homomorphisms preserve the
scalar and addition. `algHom_mem_degreeFiltration` then uses the submodule
power induction: the scalar case has degree zero, sums stay in the same
piece, and a product with a degree-one factor increases degree by one.

`algEquiv_mem_degreeFiltration_iff` applies this result to an algebra
equivalence and its inverse. Its two generator hypotheses are explicit;
there is no assertion that an arbitrary algebra equivalence preserves degree.
These results do not require an injective generator map, a PBW theorem,
finite-dimensional Lie algebras, or characteristic zero.
