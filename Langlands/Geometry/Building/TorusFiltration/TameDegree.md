# The degree of a tame extension over the maximal unramified field

`not_dvd_finrank_of_tame` applies to a finite intermediate field
over `inertiaFixedField F`. From `IsTamelyRamifiedOverUnramifiedClosure`
it proves that its degree is prime to the residue characteristic of \(F\).

The original uniformizer has order one and generates the maximal
ideal of the base integer ring. `maximalIdeal_before_eq_span_uniformizer`
then identifies the same generator in the unramified integer ring.
The valuation ring of the finite extension is the finite integral
closure and is a local principal ideal domain. The map of integer
rings is local. The residue extension is integral over the
algebraically closed unramified residue field, so its inertia degree
is one. `Ideal.sum_ramification_inertia_eq_finrank` and
`IsIntegralClosure.rank` identify the exponent of the extended
maximal ideal with the field degree.

Writing the base uniformizer as a unit times a power of an extension
uniformizer shows that the normalized additive value of the latter
times the extension degree is one. The exponent in the tameness
predicate sends that same value to a base value. Base values of
nonzero elements are integers by
`algebraicExtensionAddValuation_base_of_ord_eq`. Thus the extension
degree divides the tameness exponent, which is prime to the residue
characteristic.

The argument verifies the value-group formulation of tameness used
in `KPWeaklyInducedTorus`, which implements Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Definition B.6.2.
