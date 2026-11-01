# Actual source-cut orbital integral comparison

This internal construction compares the actual quotient coordinates, coefficient
projections and compact stages integrals for source shapes `B` and `D` with
`B.cuts ⊆ D.cuts`. It assumes that `w` increases on each source block of `B`.
The target shape `C` and the supplied p-adic field and topology are fixed.

The generic `leftQuotientHomeomorph` descends a continuous group equivalence
which identifies its two specified subgroups. Both directions are constructed
with the actual quotient relation, and the representative formula is literal.
For the orbit problem, both nested kernels are continuously identified with the
same target radical. Their composite preserves the underlying parabolic group
element. The proved source-cut equality of the radical intersections therefore
identifies the actual nested intersections. This supplies
`parabolicOrbitNestedQuotientCutHomeomorph`, including its representative formula.

For an arbitrary ambient complex representation `ρ`,
`cutOrbitNestedCoefficient` is the existing positive-half inducing coefficient
of the actual normalized Jacquet representation, restricted to the actual
nested intersection. `cutOrbitCoefficientMap` descends the actual source
Jacquet quotient projection to these two coefficient coinvariants. To verify
the relations, the proof lifts a Jacquet class to an ambient vector, uses
`Transition.inducing_mk` to cancel the positive inducing and inverse Jacquet
half factors, and transports the intersection element through the common
radical coordinate. Its ambient matrix is unchanged, so the target
coinvariant relation proves the required equality. The map sends the class of
`x` to the class of `Transition.quotient ... x`.

`cutOrbitSimple_comp` uses genuine `quotientCoinvariantSimple` functions from
compactly induced kernel functions. Its hypothesis says that the target
function is pointwise the actual source Jacquet projection after the kernel
coordinate equivalence. Quotient induction and the representative formula for
`cutOrbitCoefficientMap` prove the simple-function equality. For any quotient
measure finite on compact sets, `cutOrbitIntegral_map` integrates this equality
against that measure on the source and its actual pushforward on the target.
The proof combines measurable change of variables with linearity of the
finite-fiber algebraic integral. Finite-measure support follows from the proved
compact-support property of the actual descended functions. No topology on the
coefficient vector spaces is required.

For an actual smooth ambient representation `A`, `cutOrbitKernelSlice` is the
existing `splitStagesKernelSlice` applied to the actual parabolic stabilizer,
stages subgroup, Levi projection and section. Smoothness of its covariance
representation follows from smooth normalized Jacquet and the smooth positive
half character. Its value at a kernel element `x` and a Levi point `l` is
exactly the original orbit function at `x * s(l)`. `cutOrbitIntegrand` forms the
genuine descended simple function from this compact slice, with the canonical
Borel measurable structure on the quotient. Its representative value is the
coefficient coinvariant class of that same original function value.

`cutOrbitStagesIntegral_map` applies the preceding integral comparison to these
actual compact stages slices. It quantifies over compact orbit functions for
`B` and `D` whose values on the target parabolic are related by the actual
Jacquet quotient projection. Their slices satisfy the required relation
because the kernel coordinate equivalence preserves the underlying parabolic
element. Consequently the actual stages integrals commute with
`cutOrbitCoefficientMap` using one measure and its pushforward.

All constructions retain arbitrary primes, supplied fields and topologies,
independent field and coefficient universes, and every natural rank including
zero. The generic simple-function comparison also permits any topological ring
structure on the field carrier; the actual stages specialization uses the
supplied topology. No irreducibility, admissibility, finite-dimensionality,
positivity or classification result is used.

This module is a focused prerequisite for signed effectivity. It does not yet
instantiate the pointwise projection relation with the corrected support
representatives, construct mutually compatible Haar data across source shapes,
or identify these integrals with a simultaneously chosen family of orbit
comparison equivalences. Exterior signs, lower-degree exactness, terminal
homology and signed effectivity remain separate obligations.
