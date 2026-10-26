# Admissibility inputs for relative cosocle comparison

`Langlands.RelativeCosocleAdmissibilityStatement` is a closed internal
applicability interface with independent field, Levi-carrier and quotient-carrier
universes `uF`, `uV` and `uW`. It applies to every actual p-adic field, its supplied
compatible topological datum, every natural rank including zero, every block
shape and every actual complex representation `π` of its product Levi.

The first two clauses extract admissibility from the existing analytic
`RelativeRegularComparison.IsLeviTempered` and `IsLeviSquareIntegrable`
predicates. These predicates quantify over every Borel Haar measure on the
actual Levi central quotient. Actual Haar existence makes this extraction
nonvacuous; no measure or admissibility premise is added to these two clauses.

The third clause starts with any admissible `π`. For every real vector `t`,
it asserts admissibility of the existing `T.leviRealPowerTwist B t π.ρ`, of its
actual `CuspidalJacquetMultiplicity.induced` representation, and of the target
of every surjective intertwiner from that induction. This is the existing upper
normalized induction with positive-half-modulus covariance and right translation.
The target has its own independent carrier universe.

No clause requires irreducibility, a positive parameter, strict ordering,
unitarity, a support presentation, finite length, or positive rank. This
statement asserts admissibility only.

This is derived internal content for the relative cosocle application. Its
intended route combines the existing Haar-existence theorem and analytic
definitions, open-kernel real-twist preservation, normalized-induction
admissibility, and compact averaging for surjective intertwiners. The existing
block Iwahori basis supplies compact open subgroups for every supplied topology
and every rank. It is not a transcription of a separate theorem of Silberger,
and asserts no second adjointness, Hom comparison or cosocle equality.
