# The one-group building axiom on actual anisotropic quotient data

This is a derived internal construction from the existing polysimplicial and
actual valuation-building definitions. Its input is supplied actual
`ValuationBuildingData G` and an anisotropy proof for the same group. It
retains the original reduced quotient, rational-point action, apartment,
actual torus embeddings, roots and valuation normalization. It does not
construct valuation-building data for an arbitrary reductive group.

The empty family of simplicial factors is a polysimplicial complex whose
product vertex set and facet set each have one element. A general helper
proves that any polysimplicial complex with one facet, with its whole complex
as its sole apartment, satisfies the existing four building axioms. The
unique facet is a chamber, galleries are reflexive, and there are no strict
codimension-one faces. Thickness and thinness therefore have no
codimension-one cases; the apartment isomorphism is the identity.

For a supplied actual one-point quotient, the existing building facets are
nonempty and hence each is the whole quotient. A bijection identifies them
with the empty-factor complex's facet. Its face relation agrees with the
original `FacetPrecedes` relation by reflexivity. The original apartments
fill the quotient, so their realized apartment complexes are exactly the
whole complex. Every rational point acts trivially on this quotient and the
complex, and the identity on its empty family is a polysimplicial
automorphism.

For an anisotropic actual group, the previously derived actual quotient is
a subsingleton. Every split subtorus has only one homomorphism to any group
scheme. The unique homomorphisms between the supplied maximal split torus
and any other actual maximal split torus therefore give inverse
isomorphisms and satisfy the original torus-chart equation. All conjugate
torus embeddings agree and all apartment images agree. This establishes
the existing torus/apartment correspondence without assuming a general
maximal-split-torus conjugacy theorem. The actual normalizer stabilizer
clause is the preceding root-free geometry theorem.

`anisotropicRealization` supplies the realization, and
`satisfiesBuildingAxiom_anisotropicRealization` proves all five fields of
the existing `SatisfiesBuildingAxiom` predicate at every universe `u`.
These are precisely the one-group clauses of KP Axiom 4.1.1. Building
comparisons between different groups, apartment splittings, the remaining
axiom families and unrestricted existence remain separate obligations.
