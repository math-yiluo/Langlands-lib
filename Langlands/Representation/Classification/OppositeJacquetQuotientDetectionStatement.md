# Positive opposite-Jacquet counts for quotients of induction

This internal proposition concerns the existing actual normalized upper
induction `induced T B σ` and opposite normalized Jacquet object
`oppositeJacquet`. It quantifies over every prime, p-adic field, supplied
compatible topology, positive rank and block shape. The field, inducing
carrier and quotient carrier universes are independent.

Suppose the product-Levi representation σ is irreducible and admissible,
and the admissible GL representation P admits a surjective nonzero
intertwiner from this induction. If the opposite Jacquet module of the
induction has an actual finite simple series counting σ exactly M times,
the opposite Jacquet module of P has such a series counting σ exactly m
times, with `0 < m` and `m ≤ M`. Surjectivity and nonzeroness of the
intertwiner are explicit hypotheses. P need not be irreducible.
Admissibility here includes smoothness and finite generation of invariant
subspaces for every open subgroup, with the supplied topology.

The provenance is internal. The intended proof specializes actual
coinvariant surjectivity and actual-series simple-map detection, using
admissible normalized second adjointness to obtain a nonzero map from σ
to the opposite Jacquet module of P. Positive rank and admissibility of
both σ and P retain the hypotheses of
`Parabolic.StandardSecondAdjointnessClause`. This proposition has no
second-adjointness or local Hom-equivalence premise; proving it requires
an actual proof of the needed adjointness result. First adjointness into
upper induction does not supply this map. A nonzero Hom alone supplies
no finite series; the ambient count supplies that series.

The induction has positive half-modulus covariance and right translation.
The opposite quotient uses the actual opposite radical and the inverse
upper full modulus, transported from the Levi subgroup to the product
Levi, exactly as defined by `oppositeJacquet`.

This file defines the proposition only. It proves neither this proposition
nor second adjointness, admissibility of a particular input, an ambient
count, unconditional Jacquet finite length, a map between different
inductions, or a segment constituent. Its sole project import is
`CuspidalJacquetMultiplicityStatement`, supplying the actual objects and
multiplicity predicate. No classification conclusion is assumed.
