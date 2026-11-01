# The actual quotient for a pair of open orbit supports

This internal construction extends the published orbit-restriction assembly to
any pair of open invariant subsets of the actual inducing quotient whose set
difference is a specified single orbit. It does not require an enumeration of
the other orbits or an identification with an existing ordered filtration.

`OpenOrbitSupportPair P Q w` records the lower and upper subsets of `P \ G`,
their invariance under right translation by `Q`, their openness, their
containment, and the equality of their difference with the actual orbit of
`P w⁻¹`. These are geometric data about the actual subsets. The orbit is
locally closed and is closed relative to the upper subset.

`restriction_zero_iff_lower` proves the kernel assertion directly: for a
covariant smooth function supported in the upper subset, its values at
`w⁻¹ q` vanish for every `q` precisely when its support lies in the lower
subset. The forward direction uses the difference equality and the constancy
of vanishing on left cosets; the reverse direction uses disjointness of the
lower subset from the new orbit.

For closed `P` and `Q` in a locally compact sigma-compact topological group,
`restriction` uses the published canonical orbit homeomorphism to restrict
actual compactly induced sections to the actual conjugated orbit piece. This
is a natural transformation for every commutative coefficient ring and smooth
inducing representation, and its kernel is exactly the pulled-back lower
support subrepresentation.

For complex coefficients in a nonarchimedean Hausdorff group,
`restriction_surjective` invokes the published proved compact orbit-section
extension, with the specified upper open set. No extension assertion is assumed
as an additional hypothesis. The existing first isomorphism construction gives
`quotientIso`, a natural isomorphism from the actual upper-support quotient by
the lower support to the actual compactly induced orbit piece. Its projection
formula states that each representative is sent to its actual orbit restriction.
The representation-carrier and group universes remain independent.

The provenance is internal: the new content combines the published actual
orbit restriction, orbit homeomorphism, compact section extension, and
subfunctor quotient constructions. It supplies no Jacquet quotient comparison,
coefficient integral, cross-parabolic compatibility, exterior sign or exactness
result. A concrete corrected support filtration must still prove its own
single-orbit difference equality before using this construction.
