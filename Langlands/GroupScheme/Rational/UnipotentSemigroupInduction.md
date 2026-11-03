# Central dimension induction for exact unipotent semigroup products

This internal derived unit assembles existing vector products and central
extension descent. It retains augmentation/Lie containment, semigroup
realization, smooth quotient comparison, intersection comparison, existence of
a central stable vector subgroup, and existence of its smooth quotient as
explicit premises. It does not prove any of these inputs or the full
`SemigroupOrderedProductStatement`.

`points_eq_one_of_range_id_eq_bot` reads triviality of the identity range on
each scheme test. The identity of each point factors through the identity map,
so equality of its range with the bottom subgroup makes that point the unit.
Consequently ordered multiplication of any finite number of copies of this
group is bijective on all tests. `trivialOrderedProductIso` is the resulting
actual scheme isomorphism with the original ordered multiplication as its
forward map. It includes the empty product and makes no field or smoothness
assumption.

For a smooth connected affine ambient group with trivial identity range,
`hasOrderedSemigroupProducts_of_range_id_eq_bot` uses the ambient group itself
as every factor. Every subgroup functor equals both the bottom and the top,
so these factors represent the actual semigroup subgroups. Their original
ordered multiplication is `trivialOrderedProductIso`.

`unipotentSemigroupOrderedProduct_of_centralStatements` proves exactly the
existing `UnipotentSemigroupOrderedProductStatement` under its six explicit
premises, at arbitrary universe `u`: the field `k` is algebraically closed,
the ambient group is smooth, connected, affine and unipotent, `S` is a split
`k`-torus, and `b` is its actual automorphic action on that group. The proof
first obtains a common natural relative dimension from smoothness and
connectedness. Strong induction on
that dimension treats the trivial identity range by the preceding construction.
Otherwise the central subgroup premise supplies an actual smooth connected
central vector subgroup, its original linear action, coordinates, positive
relative dimension, and equivariant inclusion. The quotient premise supplies
an actual smooth affine connected unipotent fppf quotient with strictly smaller
relative dimension and its equivariant action. The vector coordinate product
theorem gives the exact product property on the central subgroup, and the
induction hypothesis gives it on the quotient. The existing central extension
assembly then gives it for the original ambient action.

The implemented induction needs no separate classification of dimension-zero
groups: in the nontrivial branch the quotient premise itself gives a strictly
smaller natural number. All partitions, including empty index sets and
occurring zero weights, are handled by the imported exact product properties.
The cross-exclusion remains between each original block and the other block's
positive additive semigroup; no disjointness of generated semigroups is
introduced. The scalar-extension and solvable reduction and all six premises
remain separate obligations for the full host theorem.
