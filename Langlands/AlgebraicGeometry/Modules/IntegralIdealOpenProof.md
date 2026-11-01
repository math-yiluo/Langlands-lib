# The unit locus of a nonzero ideal

This proof derives `IntegralIdealOpenStatement` from actual local sections.
A nonzero ideal monomorphism must have a nonzero value on some local
section: otherwise every component would be zero, and monicity would force
the source to be zero. Restrict to that open and form the section morphism
from its structure module into the ideal. Composing with the ideal
inclusion gives a structure-module endomorphism with nonzero scalar
coefficient `c`.

Reducedness implies that the basic open of `c` is nonempty. On that open
the coefficient is a unit, so the composite is invertible. The ideal
inclusion is then both monic and epic and hence invertible. Stalk
comparisons transport this conclusion through the two open restrictions
to an open of the original scheme.

For the second clause the ambient scheme is integral. Regard the entire
space as an irreducible closed set. The cokernel vanishes on the nonempty
open just constructed; the published smaller-support lemma bounds its
support height by the ambient dimension bound `d`.

The entry theorem `integralIdealOpen` packages these two conclusions.
This is an internal argument and makes no additional assertion about
coherence, filtrations, or Euler polynomials.
