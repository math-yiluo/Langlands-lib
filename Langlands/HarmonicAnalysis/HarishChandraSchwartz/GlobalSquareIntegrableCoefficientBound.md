# Global coefficient Xi bounds from square integrability

This internal module extracts an order-zero consequence of the published
`RationalSquareIntegrableDecayProof.exists_geometric_coefficient_bound` and
combines it with `CentralSubgroupSquareIntegrabilityTransfer`. It preserves
the existing rational-point Xi function and the original coefficient. It is
a derived prerequisite for the wave-packet and positive-constant-term
arguments, not a new original-literature assertion or an exact VI.3.1 proof.

`hasXiBoundedCoefficients_of_splitComponentSquareIntegrable` takes a connected
reductive group over any nonarchimedean local field, a maximal split torus
and generic cocharacter, the compact open Iwasawa data defining
`rationalXi hKc hPK`, and a compact subgroup `K0` with
`SimultaneousStandardBasisAt` and `FiniteCartanCovering`. Its representation
is any smooth representation square integrable modulo the actual point image
of a split component, with the displayed Haar measure on the canonical
Borel quotient. It concludes `HasXiBoundedCoefficients` on the entire group.

The proof uses the finite chamber-lattice decomposition from the published
rapid-decay proof. It chooses one positive generator per simple root and a
finite set of remainders modulo the common zero-pairing lattice. The finite
Cartan cover supplies a finite set of compact translates. For every fixed
smooth coefficient, the published geometric estimate on those translates
provides one constant `C` and one `0 < q < 1`, uniformly in all nonnegative
lattice exponents. Every group point is the product of a central uniformizer
power and one of these translates. The original unitary central character
removes the central factor from the coefficient norm; the published central
invariance theorem removes it from Xi. Since `q` to the sum of the exponents
is at most one, the positive constant `1 + max C 0` bounds the coefficient by
Xi everywhere. This also covers the empty simple-root type: the sums are zero
and the geometric factor is one.

This argument requires neither a matrix representation or height parameter,
nor a norm-kernel restriction or a valuation-image finite-index premise. It
uses geometric decay only at order zero and makes no full-height rapid-decay
claim on the entire group.

`hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable` takes the same
geometric and Xi data and an irreducible admissible representation square
integrable modulo any normal central subgroup `C`, with the original displayed
Haar measure and explicit Borel compatibility on `G(F)/C`. The subgroup `C`
need not be closed. The proof chooses an auxiliary Haar measure on the
canonical actual split-component quotient, transfers square integrability
by `isSquareIntegrable_splitComponent_of_centralSubgroup`, and applies the
preceding estimate to the same representation. No relation between `C` and
the split-component image, and no valuation index, is assumed. The supplied
split component and the structural basis/Cartan data remain explicit inputs.

`centralSubgroupXiCoefficientConstant` selects a positive constant from this
proved estimate for each original vector and smooth functional. Its
`_spec` theorem gives positivity and the bound at every actual group point.
The field and representation-carrier universes remain independent throughout.
There is no splitness or quasisplitness assumption on the ambient group and
no characteristic restriction.

The module proves no existence of the retained structural data, no uniform
bound over all vectors at a fixed coefficient level, no constant-term identity
or exponent realization, and no full wave-packet Schwartz membership. Those
steps remain distinct from this global coefficient estimate.
