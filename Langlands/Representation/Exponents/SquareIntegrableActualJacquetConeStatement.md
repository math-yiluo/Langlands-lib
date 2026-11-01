# Strict cones for actual scalar Jacquet subquotients

`Langlands.SquareIntegrableActualJacquetConeStatement.{uF,uV}` is an internal
derived interface for analytic square integrability. The p-adic field and
representation-carrier universes are independent. The supplied compatible
`T` fixes the topology and residue-normalized absolute value throughout.

For every positive rank, actual smooth representation `π` with the existing
analytic `T.IsSquareIntegrable π.representation`, block shape `B`, and nonzero
actual smooth subquotient `S` of the normalized upper Jacquet object, suppose
block scalars act on `S` through `χ`. Every supplied real part `x` of `χ` then
has zero full sum and strictly positive proper prefix sums, in the conventions
of `Exponents.IsPositiveRootCone`. The character and the real part are supplied,
not asserted to exist by this interface.

There is no irreducibility hypothesis on `π` or `S`, and no additional
admissibility, finite-length, global spectral decomposition or support premise.
The actual subquotient relation includes an invariant subspace, its actual
quotient, and an isomorphism to `S`; a class or support equality does not replace
this hypothesis. The analytic predicate retains its central-quotient Haar and
smooth-dual matrix-coefficient definition. This statement supplies no proof.

The provenance is project-internal composition of the published local central
scalar-subquotient detector, local central dual-to-primal conversion, strict GL
square-integrability exponent criterion and elementary character/cone
comparison. It is intended as an adapter for actual cuspidal tensor occurrences;
it does not construct one, put its factors on a single integral line, or imply
a classification statement on its own.
