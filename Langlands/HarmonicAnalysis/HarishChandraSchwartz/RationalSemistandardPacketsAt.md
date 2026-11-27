# Actual semistandard packet data at a common compact

`packetsAtCompact` constructs the opposite scalar data of each actual
twist orbit. It uses the orbit's square-integrable inducing representative.
The dynamic normalization transports the original split-central quotient
Haar to the cocharacter realization, and the whole-domain continuation
theorem supplies both standard intertwiners at the prescribed subgroup.
The packet constructor uses the regular inverse composition scalar
from these two intertwiners.

When the subgroup is the source special compact, the compact picture of
each coefficient fiber and the scalar data of each packet use that exact
subgroup. For the Haar measures of the source quotient traces,
`sourceQuotientHaar_intrinsicNormalization` verifies the existing
`IntrinsicQuotientNormalization` for the same pictures. The construction
provides the inputs to the packet integral and weighted synthesis.

Waldspurger (2003), I.1, printed p. 240, fixes the compact normalization.
IV.1.1, p. 278, and IV.3, pp. 285–287, use the rational standard
intertwiners and their opposite composition. V.2.1, pp. 292–293, uses
the regular unitary density, and VI.3, pp. 301–302, integrates it
against the induced coefficients.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
