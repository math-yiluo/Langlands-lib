# Arithmetic of the subfield integer ring

The integral closure used by `MinimalElement` agrees with the integer
ring of the spectral local-field structure on a finite extension. The
identity on underlying field elements induces the comparison ring
isomorphism. Discreteness and the field-of-fractions property follow
from that comparison.

For the maximal-ideal computation, the base maximal ideal has exactly
one prime above it in the extension integer ring. The ideal
factorization formula therefore identifies its extension with the power
specified by `subfieldRamificationIndex`. Equality of principal ideals
then gives the uniformizer factorization up to a unit.

These are derived arithmetic lemmas for the setting of Bushnell–Kutzko
(1993), §1.2, printed pp. 24–25, and (1.4.14), printed p. 41.
