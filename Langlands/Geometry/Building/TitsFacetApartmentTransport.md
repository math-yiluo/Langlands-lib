# Tits comparison on actual building apartments and facets

This unit transfers the abstract restricted-apartment comparison to the existing
KP quotient of supplied parahoric building data. Under the existing
`IsBuildingTitsSystem` predicate, two actual apartments containing the same two
facets admit an element of `G(F)^0` carrying the first apartment to the second
and stabilizing both facets setwise. `twoFacetApartmentTransport` chooses such
an element in the intersection of their actual zero-subgroup stabilizers.

The proof uses the predicate's precise facet-to-parabolic bijection and equality
of apartment families. It does not identify the base apartment with the standard
restricted apartment. For each apartment, choose its representative in the
restricted family. Stabilizers are equivariant under conjugation because they
are the stabilizers for the original action of `G(F)^0`. An apartment is the union
of the actual facets contained in it, so injectivity of the facet-to-parabolic
map shows that the set of those parabolics determines the actual apartment.
Apply `restrictedApartmentPairTransport` to the two chosen representatives and
transfer its image equality back to the quotient subsets.

All translation, containment, coverage and equivariance facts in this module are
internal deductions from the original facet and apartment definitions and the
existing Tits-system predicate. The source motivation is Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Proposition 1.5.6(5), printed pp.56–57
/ PDF pp.87–88, and Axiom 4.1.9. The subgroup comparison implementing the
double-coset argument is imported from `TitsApartmentPairTransport`.

The conclusions concern the original quotient and its original group action at
every universe parameter. Setwise stabilization is the exact conclusion here.
Pointwise fixation in affine facets, apartment-distance compatibility for an
arbitrary pair of points, and the complete NPC building metric remain separate
obligations.
