# Rational points are dense in actual adelic projective space

Worker 208. Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.10, Example 4.3, proves that rational points of
positive-dimensional projective space are dense in its adelic points. The two
arithmetic clauses here state that conclusion for the actual relative
polynomial-Proj scheme `projectivePointScheme`, also allowing dimension zero,
where the same density conclusion holds.

The source of each displayed map is the actual set of relative scheme
morphisms `Spec F → Pⁿ_F` over `Spec F`. Its value is scalar extension through
the original diagonal algebra map from the global field to its original
adele ring. In particular, this is the principal rational-point map, rather
than a chosen dense parametrization.

The target topology is `curvePlaceProjectiveAdelePointTopology` or
`numberFieldProjectiveAdelePointTopology`. These were constructed independently
from the actual projective model over the corresponding ring of arithmetic
integers, the topology on its arithmetic levels, and the canonical
generic-fiber identification. The statement assumes no full-product comparison
or density theorem as an input.

The function-field clause permits arbitrary finite constants, any specified
finite extension of their rational-function field, and the compatible scalar
tower, without imposing separability. The number-field clause uses the full
adele ring, including every infinite factor. Both clauses quantify over every
finite initial arithmetic set, including the empty set, and an arbitrary
common universe. The dimension-zero extension is an elementary addition to
the source's positive-dimensional formulation.

`AdelicProjectiveRationalDensityStatement` is exactly the conjunction of these
two Prop-valued targets. This file states density. The proof and the distinct
positive-dimensional conclusions that the rational image is a proper subset,
is not closed and is not discrete remain separate obligations.
