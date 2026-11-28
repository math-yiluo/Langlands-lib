# Smooth vector lifting for a Banach quotient

`SmoothBanachQuotientStatement` applies to two jointly continuous
representations of the units of a finite-dimensional real Banach algebra on
complex Banach spaces. The algebra and the two carriers have independent
universes. If `T` is a surjective bounded equivariant map between the Banach
representations, each genuine smooth vector of the target has a genuine
smooth preimage under `T`.

## Proof

The factorization of `SmoothVectorSubgroupFactorization` for the whole
units group gives a finite sum of smooth compact averages, initially
expressed by evaluation against continuous linear functionals on the
smooth carrier. The exponential charts of the top subgroup agree with
the units charts by `contMDiff_units_iff_top`. A continuous group
equivalence transports the Haar integral and the compact support of the
kernels. Composing each kernel with inversion matches the convention
of `smoothedVector`.

Evaluating the factorization on bounded functionals after the empty-word
map and commuting them with the integrals gives the same finite sum in
the Banach space. Hahn–Banach separates any nonzero difference, proving
the vector identity `exists_sum_smoothAverage_units`.

Lift each vector in the target factorization through the surjective Banach
map. Applying the same kernels in the source gives smooth vectors by
`BanachOrbitSmoothing`. Bounded linearity commutes with the Bochner
integrals, and equivariance carries the source averages to the target
averages. The sum of the source averages is the required smooth lift.

This is the exactness consequence of the Library's smooth-vector
factorization for an actual Banach quotient.
