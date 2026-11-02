# Upper triangular maximal solvable containment

This internal helper proves maximality among abstract solvable subgroups over
an infinite field. Its source motivation is Milne, *Algebraic Groups* (2017),
Definition 17.6 and Example 17.7, printed pp.353–354 (one-based PDF pp.369–370),
source ID `milne-2017-algebraic-groups`. The conclusion strengthens the algebraic
maximality needed for the Borel subgroup application, which uses an algebraically
closed field. This is a derived internal proof route, rather than Milne's
Lie–Kolchin proof of Example 17.7.

The theorem `exists_lower_transvections` works over any field. Given an abstract
subgroup `H` containing the upper triangular subgroup and containing an element
outside it, the published upper triangular Bruhat factorization places the
permutation factor of that element in `H`. This permutation cannot be the
identity. A nonidentity permutation of a finite ordered set has an inversion:
a monotone permutation would be the identity. Conjugating all transvections of
the corresponding upper root group by the permutation factor places a full
lower root group in `H`.

Over an infinite field, `not_isSolvable_of_not_le` then applies
`OppositeRootNonsolvable.not_isSolvable`. The required opposite upper root group
already lies in the upper triangular subgroup. Consequently `H` is not solvable.
The theorem `eq_upper_of_isSolvable` restates this result: any solvable abstract
subgroup containing `upperTriangularSubgroup n K` equals that subgroup. There
is no restriction on the characteristic, and no closedness, connectedness or
algebraicity hypothesis is needed for `H`.
