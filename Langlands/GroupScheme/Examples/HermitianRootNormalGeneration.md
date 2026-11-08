# Normal generation by the actual Hermitian upper rational points

This internal unit proves normal generation by the actual upper rational points
of the weighted Hermitian group scheme under middle anisotropy. The scheme data
are a separable quadratic extension of fields `L/k`, a finite middle index in
`Type`, a conjugation-fixed diagonal form `H` and unit witnesses for its weights.
The common field universe is arbitrary, and every characteristic is allowed.

First, over any commutative ring with involution and any finite middle index,
`Parameters.normScale r` scales the vector coordinate by `r` and the scalar
coordinate by `r * bar(r)`. The pairing scaling identity proves that this gives
a parameter, and the two coordinate formulas prove multiplicativity.

Over a field, the previously constructed pure trace-zero reflection is an actual
determinant-one isometry. For a nonzero trace-zero scalar `s`, the theorem
`traceZeroReflection_conjugate_embedding` proves that conjugating the upper
parameter `normScale (bar(s)) x` by that reflection gives exactly the prescribed
opposite parameter `x`. The proof evaluates the existing reflection matrix and
its inverse and checks each block entry.

The original rational matrix equivalence transports this reflection to an actual
`weylPoint`. Its conjugation formula follows by injectivity of that equivalence.
Quadratic conjugation supplies a nonfixed scalar `a`, and `a - bar(a)` is a
nonzero trace-zero scalar, including in characteristic two. Consequently every
normal subgroup containing the actual upper rational family also contains the
opposite rational family. The previously established two-root generation theorem
then gives `eq_top_of_normal_upper_range` when `H.IsAnisotropic` holds.

The provenance is internal: these results derive from the implemented finite
weighted Hermitian pairing, actual elementary pure reflections, rational-point
comparison and two-root generation. They make no classification assertion for
general reductive groups and do not establish unrestricted local Kneser–Tits.
