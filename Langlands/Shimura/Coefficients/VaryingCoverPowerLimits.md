# Ordinary coefficient-power limits of associated sheaf diagrams

Author: Worker 13.

This internal construction takes ordinary inverse limits of the two published
coefficient-power systems over varying finite geometric torsors. The limit is
taken only over the full opposite category of natural numbers, including zero.
The arbitrary cover index remains independent.

The inputs are a commutative ring `R`, an ideal `I`, a scheme `X`, a category
`J`, a group diagram `D`, and an equivariant diagram of actual small-etale
covers `Y`. Every cover satisfies the existing `IsFiniteGeometricTorsor`
predicate. The scalar ring, scheme, group carriers and coefficient-module
carriers share universe `u`; the cover-object and cover-morphism universes
are independent. No limit over `J` is required.

Write `A(M)` for the published associated sheaf diagram,
`P_n(M)` for the actual power quotient of the coefficient diagram, and `Q_n`
for sectionwise power reduction followed by sheafification.
`etaleAssociatedCoefficientPowerLimit` sends `M` to the ordinary limit of
`n ↦ A(P_n(M))` in the category of `J`-diagrams of module sheaves on the
actual small-etale site of `X`. `etaleAssociatedSheafPowerLimit` sends it
to the ordinary limit of `n ↦ A(M) ⋙ Q_n`. Both are functors in every
equivariant coefficient-diagram morphism. These limits exist by the
published module-sheaf limits and Mathlib's pointwise functor-category
construction; a limiting cone is not additional input.

`etaleAssociatedPowerLimitComparison` applies the ordinary limit functor to
the published comparison of the complete power systems. Its projection
equation is the original canonical comparison at every coefficient power.
It is a natural transformation between the two limit functors.

`etaleAssociatedSheafPowerCone` has vertex `A(M)` and the genuine sheaf
quotient maps as legs. The existing quotient-transition equation proves
their compatibility. Postcomposition with the published system comparison
gives `etaleAssociatedCoefficientPowerCone`. Its leg at `n` equals `A`
applied to the actual coefficient-diagram quotient unit, by the published
whole-diagram unit equation.

`etaleAssociatedSheafPowerLimitUnit` is the universal map from the first
cone. Its naturality follows from naturality of the genuine sheaf quotient
unit and the uniqueness of maps into a limit. Composing it with the limit
comparison gives `etaleAssociatedCoefficientPowerLimitUnit`. Its projection
equation is exactly `A` applied to the coefficient quotient map, so it is
also the universal map from the second cone. The equations are equalities
of maps of entire cover diagrams.

The two evaluation isomorphisms identify the object of each limit diagram
at `j` with the ordinary limit of its evaluated coefficient-power system.
For sheaf powers, that target is exactly the existing
`Langlands.Sheaf.AdicSystem.inverseLimit` of `A(M)_j`. Their projection
equations identify the actual limit projections with the evaluated
diagram projections.
Under these isomorphisms, evaluating the limit comparison equals the limit
of the original `constantAssociatedReductionSystemsComparison` at that
cover. The final equation identifies every projection of the evaluated
sheaf-limit unit with the original sheaf quotient map.

The provenance is internal composition of
`VaryingCoverPowerSystems`, `Sheaf.AdicSystem`, and the pinned Mathlib
`CategoryTheory/Limits/HasLimits.lean` and
`CategoryTheory/Limits/FunctorCategory/Basic.lean` at commit
`5ed2965256430c3649e86755f9576b54eca72435`. The comparison and its
quotient-unit equation are reused unchanged; the new proofs use the
ordinary limit universal property, quotient naturality and evaluation
preservation of limits.

These are ordinary limits in module-sheaf categories. The construction
does not assert that the comparison or either unit is invertible, that
completion commutes with associated sheaves, or that the limit is a lisse
adic sheaf. Harris-specific torsors, diagonal indexing, smoothness, derived
limits and cohomological comparisons remain separate obligations.
