# Canonical target coefficient fibers for compositions

This module supplies the fiber identifications for the composition and
identity relations of Waldspurger V.3.2. It works with the actual rational
conjugating elements. The equality of the once-conjugated and twice-conjugated
Levi anchor cocharacters uses `GroupScheme.innerIso_mul_hom` in the order
in which the acted-on representation is first conjugated by `t`, then `s`.
The cocharacter for the identity arrow is identified using
`GroupScheme.innerIso_one_hom`. Its inverse-conjugation counterpart follows
from the multiplication and identity equalities.

`multiplicationTarget` transports the presentation of the direct target
parabolic through that cocharacter equality, keeping its cocharacter and
Iwasawa factorization. `multiplicationEquiv` uses the
actual inducing-twist comparisons on the source parameter, the transported
parameter and the product-conjugated parameter. The two successive pullbacks
are identified with inverse-conjugation pullback along the product by
`conjugationFunctorCompIsoApp`, whose linear map is the identity on the
original representation carrier. Changing anchor pulls the inducing object
back under the identity on points of the two equal literal Levi subgroups.
The same-Levi `coefficientCongr` applies the inducing identification to the
product-normalized induction and its smooth dual, and inverse left
translation by the identity identifies the two anchor presentations.

`identityTarget` and `identityEquiv` apply the same construction to the
identity point. `inverseTarget` and `inverseEquiv` use the identity
conjugation after composing pullback by a point with pullback by its inverse.
These target equivalences use the actual parameter and inducing-object
transports and retain the full external product action. They support
subsequent statements of the composition and inverse laws.
