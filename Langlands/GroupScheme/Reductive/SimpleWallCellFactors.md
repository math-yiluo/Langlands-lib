# Dynamic limits of ordered root products on a simple wall

This internal construction gives the generic dynamic factorization of
ordered root products needed for the simple-wall cell argument. It combines
the published coordinate root-subgroup and dynamic-limit APIs, with no
field, reducedness, smoothness, affineness or reductivity hypothesis on the
ambient group. Actual root parametrizations are supplied.

`rootProductZeroPart` is the ordered product in which every factor with
nonzero coordinate pairing against a chosen integral cocharacter is replaced
by the identity. The remaining factors are the original root points. Its
definition is independent of whether the nonzero weights are positive.

`IsRootParametrization.rootPoint_mem_dynamicCentralizer` puts every
zero-weight root point in the actual dynamic centralizer, using the
root-parametrization representation and the published zero-pairing
root-subgroup containment. Closure under products then proves
`rootProductZeroPart_mem_centralizer` on every test scheme.

`orderedProduct_hasLimit_zeroPart` assumes every factor's pairing is
nonnegative. A zero-weight factor has itself as its limit because it
centralizes the cocharacter. A positive-weight factor has identity limit,
by the general-base contraction theorem in `CorootSimpleWall`. Induction
on the ordered list and multiplicativity of dynamic limits give exactly
the stated zero-weight product as limit. Thus the result concerns actual
orbit extensions on all relative scheme tests, including tests with
nilpotents.

The next two lemmas remove this limit on the left or the right of the
original ordered product. The limit itself centralizes the cocharacter,
so it has its own constant limit; inversion and multiplication then show
that each resulting point has identity limit. This is membership in the
actual dynamic unipotent subgroup. No uniqueness of limits is needed.

Finally `rootProductZeroPart_eq_single` assumes exactly one factor has zero
pairing and proves that the zero-weight product is precisely that root
point, at its original coefficient. The proof uses the published ordered
list product lemma with every other factor equal to the identity.

These lemmas do not yet identify the rank-one component of an equality
between two full big-cell points or prove the negative-simple translation
law.
