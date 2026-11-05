# Cartan structure over algebraically closed fields and the remaining input

Author: Worker 1588.

This internal construction combines published Cartan centralizer,
central-torus quotient and no-torus results. It supplies a uniform
nilpotence bound for Cartan subgroups over algebraically closed fields and
reduces the exact arbitrary-field `CartanStructureStatement.{u}` to the
single explicit input `FiniteFieldGeometricMaximalTorusStatement.{u}`.
It does not prove that remaining input or the unrestricted target.

Let `k : Type u` be algebraically closed, let `G` be a smooth connected
affine group scheme over `Spec k`, and let `j : C → G` be an actual Cartan
embedding. There are no prior smoothness or connectedness assumptions on
`C`. The published construction `hj.centralTorusQuotient` supplies a
central maximal torus in `C` and its actual smooth connected affine
quotient. The quotient receives only trivial torus homomorphisms.
Over an algebraically closed field the published absolute no-cocharacter
criterion makes this quotient unipotent. Its central kernel then gives
a uniform lower-central-series bound on the points of `C` over every
relative scheme test.

The theorem
`IsCartanSubgroup.exists_hasUniformNilpotentPoints_of_isAlgClosed`
applies this existing quotient result. The definition
`IsCartanSubgroup.nilpotenceBoundOfIsAlgClosed` chooses a natural-number
witness; its specification theorem retains the full all-test bound
`HasUniformNilpotentPoints C d`. This choice has no asserted minimality.
The theorem `IsCartanSubgroup.isNilpotentGroupScheme_of_isAlgClosed`
specializes the bound through the published geometric-point adapter,
giving exactly `IsNilpotentGroupScheme C`, including its specified
algebraic-closure point group. Finally,
`IsCartanSubgroup.structure_of_isAlgClosed` combines this nilpotence with
the published `IsCartanSubgroup.smooth_connected` theorem.
These deductions do not use arbitrary-field forward preservation of
maximal tori.

For arbitrary fields, the theorem
`cartanStructure_of_finiteFieldGeometricMaximalTorus` retains one explicit
universe-general premise. It applies `noTorusStructuralReduction` to
that premise and the five published proofs
`nilpotentCentralTorusStatement`,
`algClosedTrivialMaximalTorusUnipotent`,
`Lie.semisimpleCentralizerSmooth`,
`Lie.semisimpleCentralizerSpanning` and
`semisimpleIsogenyReduction`. This yields the exact arbitrary-field
`NoTorusUnipotentStatement`, to which the published
`cartanStructure_of_noTorusUnipotent` applies. The result preserves finite
and imperfect fields, every characteristic, nonsplit tori and the
arbitrary universe `u`; their proof remains conditional on the displayed
finite-field input.

The provenance is internal: every mathematical implication used above
is an imported Library theorem, and the only new data is the chosen
bound. This module introduces no additional external structural
assertion. The algebraically closed conclusion is unconditional within
its stated field hypotheses. The arbitrary-field conclusion is a
reduction and is not a proof of the parent task.
