# Actual smooth coproducts of rational inertia-block objects

This internal bridge uses the existing concrete coproduct in the actual
rational inertia block. Its full-subcategory inclusion sends that cofan to
the concrete smooth direct-sum cofan. The latter is a colimit by
`SmoothRep.directSumIsColimit`, so the inclusion preserves the colimit of
each family and hence every diagram over the same discrete index type.

The indexing universe `uI` is independent of the field universe `uF`.
Carriers have universe `max uI uV`, which keeps the actual direct sum in
the ambient smooth category. In particular the construction applies to the
Hom-sized coproducts of the lifted norm-kernel generator presentations.
There are no finite-length, admissibility, cuspidality, irreducibility of
the base, or generator hypotheses.

`rationalInertiaBlockSmoothCofanIsColimit` applies preservation to any
supplied colimit cofan in the block, with its actual smooth objects and
intertwiners. `rationalInertiaBlockCofanDirectSumEquiv` then uses
`SmoothRep.cofanDirectSumEquiv` to identify its vertex with the actual
algebraic direct sum. The equivalence is the summation map given by the
supplied cofan's legs.

The closure and concrete block cofan are reused from
`RationalInertiaCoproducts`; the general comparison of a smooth cofan
with its direct-sum carrier is reused from `CoproductCompression`.
This module adds the inclusion-preservation bridge. It proves no
small-progenerator predicate or compression-stability result.
