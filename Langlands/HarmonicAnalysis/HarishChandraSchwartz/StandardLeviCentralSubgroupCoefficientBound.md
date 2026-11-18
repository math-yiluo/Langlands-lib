# Global Xi bounds on the literal standard Levi for arbitrary central quotients

This internal adapter combines `GlobalSquareIntegrableCoefficientBound` with
the published point, representation, quotient-measure and Xi comparisons for
an actual standard Levi. It is a derived prerequisite, with no new
original-literature assertion. It strengthens the earlier internal
`StandardLeviSquareIntegrableCoefficientBound` interface by allowing an
arbitrary central subgroup and requiring no valuation index or matrix
representation.

Fix a connected reductive group over any nonarchimedean local field, a
maximal split torus and a generic cocharacter. For a finite simple-root set
`I`, write `M` for the literal subgroup `standardLeviPoints i ν (rootSet i ν I)`
and `L` for its representing Levi scheme. The input representation `pi` is the
original irreducible admissible representation of `M`. Its square integrability
is modulo any normal central subgroup `C`, for the displayed Haar measure
`mu` on `M/C` and an explicitly Borel-compatible quotient measurable space.
The original `C` need not be closed.

`hasXiBoundedCoefficients_standardLeviCentralSubgroupSquareIntegrable` proves
`HasXiBoundedCoefficients (rationalLeviXi hKc hMK) pi.obj.representation` at
every literal Levi point. The theorem retains the compact subgroup and
Levi-Iwasawa data defining this Xi, and a compact subgroup of `L(F)` with a
simultaneous standard basis and finite Cartan cover. No structural existence
or ambient-to-intrinsic basis comparison is asserted.

The proof pulls `C` back along `leviSchemePointsEquiv`, proves that this
pullback is central using injectivity, and identifies the two actual central
quotients by `quotientContinuousMulEquiv`. It defines the intrinsic quotient
measure as the pushforward of the original `mu` along the inverse quotient
homeomorphism. The measure is Haar, and mapping it back gives `mu` exactly.
The published `isSquareIntegrableModCentralSubgroup_comp_iff` therefore
transfers the original square-integrability assertion to the same-carrier
pulled-back representation. No unspecified rescaling of the original measure
is used.

The implementation obtains a split component of the intrinsic Levi from the
published `exists_isSplitComponent_standardLevi`, applies the new global Xi
estimate for arbitrary central subgroups, and uses
`hasXiBoundedCoefficients_leviSchemeRepresentation_iff` to return to the
literal Levi and its original Xi function. The split component is chosen
inside the proof and is not an extra input to the theorem. The resulting
estimate contains neither a norm-kernel restriction nor a height or
finite-index premise.

`standardLeviCentralSubgroupXiCoefficientConstant` chooses a positive
constant for each original vector and smooth functional, and its `_spec`
theorem states positivity and the bound on all original Levi points. The
field and representation-carrier universes remain independent. The proof
imposes no ambient splitness, quasisplitness or characteristic restriction.

This coefficient estimate does not prove uniform exponent realization,
constant-term identities, full-height decay on the entire group, or the
source-normalized wave-packet Schwartz and continuity targets. The retained
structural and Levi-Iwasawa data still need to be derived in consumers that
do not already supply them.
