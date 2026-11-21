# Comparing rational Tate monodromy with a supplied model

Suppose two abelian schemes are identified after pullback to a common
scheme. At a geometric point of that scheme,
`rationalModelComparison` takes the inverse of the Tate comparison
for the model's base change, applies the Tate map of the given
identification, and then uses the Tate comparison for the original
scheme's base change. The result is a linear equivalence between
the two actual rational Tate modules at the corresponding points.

The Library's equivariance results for pointed base change and Tate
isomorphisms make this equivalence intertwine the two actions of the
common scheme's fundamental group. Thus an element that restricts
trivially on the model's base acts trivially on the original Tate
module. If the common scheme is a finite étale cover of the original
base and its fundamental group has trivial image over the model,
the uniform positive power lift to the cover proves that each
monodromy operator of the original base has finite order.

This is a derived comparison for the local monodromy argument after
potential good reduction. The finite-order corollary uses the
explicit triviality hypothesis for the map to the model's base.
