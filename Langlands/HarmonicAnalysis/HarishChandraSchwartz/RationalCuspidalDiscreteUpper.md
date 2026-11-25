# The actual rational cuspidal upper inclusion under local estimates

This derived module records and proves the local upper-inclusion step of
Waldspurger VIII.4.2 on the actual rational-point interfaces. It retains
the structural choices and the `max u uV` carrier convention of the
published equality target.

`RationalCuspidalDiscreteUpperEstimateStatement` asks for the upper
inclusion at each displayed group and Schwartz realization under three
local inputs: the central weight estimate, the ambient Schwartz L²
weight estimate for a supplied Haar measure on the group, and finite
dimension of every compact projected cuspidal bi-level span. These are
local estimates for the displayed group and choices. No assertion about
finiteness or reconstruction at other groups is assumed.

`rationalCuspidalDiscreteUpperEstimate` proves this proposition by the
actual function-representation argument in `SchwartzCentralDiscreteUpper`.
The cuspidal condition is translation stable because it quantifies over
every pair of exterior translates. The actual rational translation
weights preserve the Schwartz space. Compact-open cofinality comes from
the actual rational-point group topology. Centrality makes the given
central Haar measure right invariant. Published reductive unimodularity
gives right invariance of the supplied ambient Haar measure, and the
closed split-central quotient result gives inversion invariance of the
target's arbitrary Borel quotient Haar measure. None of these measure
invariances is an additional input.

The preceding actual construction supplies admissibility, the literal
positive quotient-L² form, square-integrability of all its coefficients,
and membership in the canonical discrete-series sum. It uses I.6.1
coefficient closure and smooth evaluation in place of the source's
convolution and reproducing-vector steps. Haar measures and their finite
comparison scalars are preserved.

This is a local estimate reduction, not a proof of either closed
VIII.4.2 target (`RationalCuspidalDiscreteCoefficientStatement`,
`RationalCuspidalFixedCoefficientLiftingStatement`). The central height and Xi
estimates and the finite projected-level input are not proved here. The finite-level input can be supplied by a local VIII.4.1
rank step; the proposition introduces no same-rank reconstruction or
VIII.1 spectral-finiteness premise.
