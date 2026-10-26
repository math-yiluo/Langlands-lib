# Admissibility for the actual relative cosocle inputs

`Langlands.relativeCosocleAdmissibility` proves the exact proposition
`Langlands.RelativeCosocleAdmissibilityStatement`. The field, Levi carrier and
outer quotient carrier retain independent universes. The proof includes rank
zero and every real block parameter.

The two analytic extraction lemmas install the topology of the supplied `T`,
the actual product-Levi topological group, and the Borel measurable structure
on its central quotient. The published
`T.exists_isHaarMeasure_leviCentralQuotient` supplies an actual Haar measure.
Specializing the universal analytic predicate to that measure gives its
admissibility component. This justifies extraction without any extra measure
or nonvacuity premise.

For an admissible Levi input, the published open-kernel real-twist equivalence
gives admissibility of the actual `leviRealPowerTwist`. The published
`Parabolic.normalizedInductionAdmissibility` then gives admissibility of the
same actual upper normalized induction used by the statement.

For each surjective intertwiner to the arbitrary target `J`, the generic
`Unramified.SphericalExistence.isAdmissible_of_surjective` passes admissibility
to `J`. Its compact-open cofinality premise is supplied directly by
`BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization` for the
same `T`, the given block shape and the identity neighborhood defined by each
open subgroup. The published generic quotient theorem uses compact averaging
to lift fixed vectors, then finite-dimensionality for fixed vectors of the
admissible source. This application uses the supplied topology in every rank.

This is an internal assembly of published elementary interfaces, with the same
provenance as the statement. It supplies admissibility for subsequent
applications of Schur's lemma, head multiplicity and admissible-input
adjointness. It proves no finite-length, second-adjointness or analytic
multiplicity-comparison assertion, and the main relative cosocle theorem
remains a separate obligation.
