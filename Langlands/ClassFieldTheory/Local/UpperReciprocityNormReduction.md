# Reduction of finite reciprocity to numerical norm filtration

This internal reduction derives finite real unit-image equalities from
`FiniteAbelianNormUnitImageCardinality.{u,u}`. It then invokes the elementary
finite reduction for the other four clauses. Its arithmetic hypothesis remains
unproved; the module supplies no unconditional proof of finite upper reciprocity.

For the upper subgroup `H` of `Gal(L/F)` at a nonnegative real level, take the
fixed field of `H` and lift it to the chosen algebraic closure. The kernel of
restriction to this finite abelian subextension is exactly `H`. Herbrand's
published restriction theorem therefore makes its upper group trivial. The
numerical hypothesis says that the image of the corresponding unit level in
its norm quotient has order one; this is a trivial subgroup, so those units are
norms. The exact finite reciprocity kernel and restriction compatibility give
containment of the reciprocity image in `H`.

Finally, the candidate's certified norm-residue equivalence identifies the
unit image in the norm quotient with the reciprocity image in `Gal(L/F)`.
The numerical hypothesis gives the order of `H`, and containment between finite
subgroups of equal order is equality. This proves literal images for every
candidate and supplied extension realization, without taking closures.

The provenance is an internal argument from the published Herbrand restriction
theorem, the Galois correspondence, the exact finite norm kernel and restriction
compatibility in the reciprocity relation, and the certified finite norm-residue
equivalence. No filtered reciprocity theorem is assumed in these steps. The new
arithmetic statement is used twice, once in the fixed subextension and once to
compare orders in the original extension.
