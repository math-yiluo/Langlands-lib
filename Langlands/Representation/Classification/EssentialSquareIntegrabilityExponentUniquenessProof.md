# Uniqueness of the real square-integrability exponent

`Langlands.Classification.essentialSquareIntegrabilityExponentUniqueness`
proves the existing
`Langlands.Classification.EssentialSquareIntegrabilityExponentUniqueness`
for every supplied p-adic field and compatible topology, with independent
field and carrier parameters `uF` and `uV`. The representation has its
original carrier in `Type (max uF uV)` and positive rank. The normalization
uses the negative real exponent, exactly as in the statement.

The proof extracts an exponent and the complete analytic square-integrability
witness from the definition of essential square-integrability.
Irreducibility gives a nonzero vector by
`FiniteIndexRestriction.exists_ne_zero`. The published theorem
`exponent_eq_of_isSquareIntegrable` then compares any other square-integrable
twist with this witness and proves equality of their exponents.

That comparison theorem extracts unitary full-center characters using an
actual Haar measure on the central quotient. Their scalar actions on the
same nonzero vector at the scalar uniformizer force equal real exponents:
the determinant norm there is a positive power of the inverse residue
cardinality and differs from one because the rank is positive. Thus no
assumed central character, invariant form, segment classification, or choice
of normalized representative is needed.

This is an internal assembly of the published analytic definition and
comparison theorem, implementing clause 6 of
`SegmentSquareIntegrabilityStatement.md`. It does not add a new literature
assertion. It proves this focused normalization prerequisite; centered
parametrization and the associated-pair induction theorem require further
arguments.
