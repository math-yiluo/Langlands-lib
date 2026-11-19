# Recovering positive real block parameters from a Cartan numerator

This internal calculation concerns tuples of real standard block parameters.
There are `r` complex slots with a positive integral weight and a complex
exponent in each slot. There are `s` real slots with a parity and a complex
exponent in each slot. The real slots retain the parity attached to each
exponent.

`numerator_apply` writes `numerator` as a sum over independent permutations
of the complex and real slots. Each complex slot has two orientations and contributes the difference
of the two Fourier modes with opposite weights, multiplied by the exponential
of twice the exponent times the logarithmic radius. Each real slot gives the
sign character times the exponential of the exponent times the logarithmic
absolute value. The sign coordinate uses its integral power, so even and odd
values cover the two signs.

The proof first shows that the product characters of the coordinate group
determine every parameter of a tuple. Evaluating in one coordinate isolates
its character. Differentiation at zero recovers the exponents and angular
weights, and evaluation at sign `-1` recovers the parities. Dedekind's linear
independence of characters then recovers the formal coefficients from the
function `numerator`.

At a tuple with all complex weights positive, only positive orientations can
contribute, and each contribution has coefficient one. Comparing the
coefficient of the original positive tuple gives a matching pair of
permutations. This is the conclusion of `exists_perm_of_numerator_eq`.

The calculation isolates the parameter recovery needed for a proof via
characters on a Cartan subgroup with one elliptic coordinate per induced
block. The connection between this formula and the characters of the actual
real standard modules is a separate representation-theoretic obligation.
