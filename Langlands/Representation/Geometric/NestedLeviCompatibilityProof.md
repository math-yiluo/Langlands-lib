# Compatibility through actual nested Levi refinements

Author: Worker 429.

`Langlands.nestedLeviCompatibility.{uA,uK}` proves the complete
`Langlands.NestedLeviCompatibilityStatement.{uA,uK}`. The parameter type
and commutative coefficient ring retain independent universes. The proof
uses the actual ordered coordinate maps and the constructed
`Geometric.flattenedLeviEquiv`, with the literal shape equality from the
statement.

For the parameter law, a helper shows that repeating a coarse function
along one refinement and evaluating it on the fine block containing a
standard coordinate gives the value on the coarse block containing that
same coordinate. The helper writes the coordinate using the flattened
shape's `indexEquiv`, applies `flatten_index`, and then uses
`blockIndex_index`. Equality elimination gives a second helper commuting
shape transport with this coordinate evaluation.

For each direct fine block, its positive size supplies its zero coordinate.
Evaluating the transported twice-repeated function there applies the
transport helper once and the parent helper twice. Applying the parent
helper for the direct refinement in reverse proves the requested
pointwise equality. Function extensionality completes the first conjunct.
This argument retains rank zero: there is then no fine block at which a
coordinate must be selected. It assumes no structure on parameter values.

For the actual inclusion law, the proof uses injectivity of
`B.leviEmbedding K`. The published `flattenedLeviEquiv_embedding` identifies
the ambient matrix of the direct inclusion and of each of the two nested
inclusions. Equality elimination on the given shape equality identifies
the direct fine embedding of the transported element with the nested fine
embedding of the original element. Thus the two included elements of the
coarse product Levi are equal. This proves actual group equality separately
from the parameter law and works over every commutative coefficient ring.

The provenance is internal finite-coordinate algebra using the published
flattening and embedding identities. The shape-transport helper generalizes
the equality-elimination pattern in
`Exponents.PositiveRootBlockSumsProof` from real values to arbitrary types;
no external mathematical theorem is invoked. The proof adds no hypothesis
and changes none of the statement's dependencies. It asserts no induced
family, analytic continuation, branch persistence, Jacquet comparison,
cone bound, multiplicity equality or irreducible head. Those remain
additional obligations in the supported all-regular comparison.
