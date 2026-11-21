# An ultrametric algebra norm for finite algebras

`finiteAlgebraNormedRing` equips a finite algebra over a complete nontrivially
normed field with the operator norm of left multiplication. A finite basis
identifies the algebra as a vector space with a finite product of copies of
the field, with the supremum norm. Evaluation at the identity shows that
the regular representation is injective. The induced norm is submultiplicative
and is compatible with the field action by `finiteAlgebraNormedAlgebra`.
The finite-dimensional module topology theorem identifies its topology
with the supplied module topology. The metric uses this supplied topology.

If the field norm is ultrametric, the vector supremum norm is ultrametric.
For operators, the maximum of the two operator bounds is a bound for their
sum, by the ultrametric inequality applied at each vector. This proves
`finiteAlgebraNormedRing_ultrametric`.

These are internal analytic coordinates for the twisted differential.
They adapt the regular representation construction used in the Library's
`Langlands.Geometry.Analytic.AffineAnalytificationFaithfulness` to arbitrary
finite algebras. Matrix multiplication, including in noncommutative matrix
algebras, and inversion on the unit locus can then use Mathlib's normed algebra
calculus.
