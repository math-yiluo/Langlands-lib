# The normalized subfield valuation and shifts of the chain

A factorization of a field unit into an integer-ring unit and a power of an
extension uniformizer expresses its chain shift as the uniformizer shift
times the exponent. The uniformizer shift is positive and independent of the
choice of uniformizer by comparison with the base period. Thus the set of
exponents in `subfieldNormalizedValuation` is a singleton for a nonzero
field element. A field unit of shift zero comes from an integer-ring unit.

Evaluation on a nonzero vector of the zeroth lattice also embeds the extension
integer ring into that lattice as a module over the base integer ring. This
proves its finite generation in the lattice-chain setting.

The constructions implement the normalized valuation in Bushnell–Kutzko
(1993), (1.4.14), printed p. 41, and its relation to the order valuation in
(1.4.15).
