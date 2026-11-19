# Products of compound matrices

`Langlands.Archimedean.CompoundMinorProduct` constructs a matrix action
indexed by one subset for each prescribed degree. A matrix entry is the
product of the minors with the chosen row and column subsets. Each minor
uses increasing enumerations.

The action follows from the Library lemma
`Langlands.GeneralLinear.Spherical.det_rectangular_mul`. Apply Cauchy–Binet
to each minor and expand the product of sums as a sum over families of
intermediate subsets. Diagonal matrices act diagonally because a minor
with differing row and column subsets has a zero row. On equal subsets
the minor is the product of the original diagonal entries at those indices.
The formula commutes with ring homomorphisms by functoriality of determinants
and products. In particular, polynomial entries can be specialized by
evaluation.

Matrix multiplication on column vectors gives a representation. A row
permutation sends a basis vector to a multiple of the basis vector indexed
by the permuted subsets. Every other collection of row subsets has a minor
with a zero row. The surviving coefficient is nonzero because the inverse
permutation gives the inverse action. For a continuous matrix family,
the finite products of determinants and matrix-vector multiplication
give continuity on each fixed vector.
