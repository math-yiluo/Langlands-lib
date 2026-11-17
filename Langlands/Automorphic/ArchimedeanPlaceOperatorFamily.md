# The finite family of actual archimedean place operators

This internal construction for Task 7294 indexes all real and complex
places together while retaining their genuine orthogonal or unitary
compact groups and their full complexified real matrix Lie algebras.
It equips the actual realization and its finite-factor multiplicity
space with the resulting heterogeneous local operator families.

Different compact-place inclusions commute. Every submonoid of the
standard full compact group containing all single-place inclusions is
the whole group: pull back to the product of the real and complex compact
factors, use finite-product generation by single-coordinate elements
in each factor, and multiply the two parts. Consequently stability under
all local compact operators gives stability under the whole compact
group.

Likewise stability under all local Lie operators gives stability under
the global complexified Lie algebra. The proof uses the published
decomposition of the underlying real Lie algebra into its place
components, extends by complex linearity, and applies tensor induction.

The actual local compact and Lie actions commute at distinct places by
the existing place covariance and zero-bracket results. Injective
evaluation at a nonzero vector of an irreducible finite factor reflects
these commutation identities to its multiplicity space. If the full
operator realization is irreducible and the finite factor is also
admissible, the published combined compact/Lie multiplicity
irreducibility therefore becomes joint irreducibility for the finite
family of all local actions.

No local model choice or invariant pairing is constructed here. This
supplies the target action-family inputs of `FiniteFamilyGKPairing`.
