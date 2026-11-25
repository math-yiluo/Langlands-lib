# Actual central simple algebras for relative finite Brauer profiles

For an actual central simple algebra over a number field with a finite
Galois splitting chart, `finiteRelativeBrauerInvariant I` applies the
relative map of a supplied invariant family `I` to the chart extended to
a finite completion. No law is assumed of `I` in this definition; for the
class-field invariant family the value is the local class-field
invariant. The base and upper fields are the actual completed fields at
the specified places. The published localization formula identifies this
value with the finite invariant of the global chart class
(`finiteRelativeBrauerInvariant_eq`).

The realization results assume that `I` satisfies `RelativeClassFormation`
and `ArithmeticNormalization` at every prime. For such a family, a finite
profile with values in the corresponding local denominator subgroups and
sum zero lifts to a relative field-unit class. The
regular descent construction realizes this class by a global central
simple algebra. Its chart is reindexed by the actual reduced degree.
The localization formula gives the specified values on that same
algebra at every finite base place. When a common positive integer
annihilates the prescribed values, the local-degree construction
supplies a Galois splitting stage with the required denominators.

The module also shows that, when every relative map of `I` is injective
(`RelativeImages`), a natural number annihilating one of the relative
invariant values annihilates the actual completed Brauer class there.
Injectivity of the relative invariant first detects annihilation of
the chart class. The additive inflation into separable-closure
cohomology carries that identity to the Brauer isomorphism.

This is an internal assembly of the Library's relative realization,
regular descent, and localization results. The constructed algebra's
degree comes from its splitting chart. Prescribing the degree needs a
further reduction by division representatives.
