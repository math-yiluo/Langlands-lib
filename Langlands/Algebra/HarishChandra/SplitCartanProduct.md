# Split Cartan subalgebras of finite products

The product of Lie algebras over a commutative ring has the coordinatewise
bracket. The instances for this structure are available under
`open scoped LieAlgebra.Pi`.
`LieSubalgebra.pi` consists of the tuples whose coordinates belong to the
given Lie subalgebras. `IsSplitCartan.pi` shows that the product of split
Cartan subalgebras in a finite product of complex Lie algebras is split
Cartan, with the conditions of `ParabolicIndependenceStatement`.

A weight vector with nonzero coordinate at a factor determines its weight
by that coordinate. Evaluating the bracket after replacing a Cartan
element by its projection to the factor leaves this coordinate unchanged.
Thus the weight factors through that factor's Cartan projection. When the
weight is nonzero, testing against a Cartan element supported at the factor
forces all the other coordinates of every vector of that weight to vanish.
Insertion in one coordinate identifies the corresponding weight spaces.

Coordinatewise abelianness passes to the product Cartan. The proof spans
the product by inserting each factor's weight spaces, using finiteness of
the index type. It identifies the zero weight space coordinatewise with
the product Cartan. For a nonzero weight, insertion into its factor
preserves the dimension of the weight space and the opposite-root bracket
with its Cartan value. A nonzero scalar multiple of that weight belongs to
the same factor, so reducedness in the factor gives reducedness in the
product.
This gives the product step in passing from split reductive Lie algebras
over the complex embeddings of a number field to the complexified
archimedean Lie algebra.
