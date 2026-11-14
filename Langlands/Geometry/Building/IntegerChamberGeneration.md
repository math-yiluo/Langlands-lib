# Generation by the actual chamber sharp fixer and normalizer

For supplied integer-valued building data `B` over any field, an order-one unit,
and an actual affine chamber `C`, `rootGroupChamberNormalizerInclusion` is the
identity inclusion from each actual relative-root group into the subgroup join
`B.apartment.sharpFixer C ⊔ normalizerPoints B.i`.

The construction uses V6 directly. An evaluated actual coroot at an order-one
unit gives a centralizer point whose translation evaluates to `-2` on the root.
Its inverse powers therefore increase the valuation of a root element by
`2*n` under inverse conjugation. For a nonidentity root point, choose a power
large enough to make its finite valuation at a chamber point nonnegative.
AS4 facet constancy identifies this depth-zero group with the chamber root
fixer. The centralizer is contained in the actual normalizer, so conjugating
back proves the required containment. The identity case is immediate.

The supporting theorem `sharpFixer_sup_normalizer_eq_top` proves generation of
the original rational-point group by this join. Actual opposite factor pairs
give disjoint indivisible positive root rays. The published ordered-product
containment then puts a generic dynamic radical in the join. Published rational
Bruhat decomposition and generic centralizer equality express every rational
point as a product of two such radical points, an actual normalizer point and
an actual whole-torus centralizer point. All four factors belong to the join.

This is an internal composition of the published integer coroot-translation,
V6, facet-constancy, root-product and rational Bruhat results. It uses no
topology or local-field instance on the underlying field, and no simply
connected comparison. It proves group generation, leaving the cover and
common-apartment conclusions to subsequent assembly.
