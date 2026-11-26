# Descent with a prescribed special reference apartment

`referenceApartmentDescent` constructs the fixed-point embedding using the
specified upper valuation class and the coefficient action on its quotient.
It applies `unramifiedValuationDescent` to the prescribed special torus and
identifies the restricted class with the supplied lower class by
`omegaCompatibleApartmentUniqueness`. The affine lift has the indicated
root pullback by `descentAffineMap_roots_of_unramifiedAffineRootRestriction`.
`apartmentDescentData` then gives the equivariant quotient embedding. A
fixed point of the upper apartment restricts to a lower valuation, and
injectivity of restriction recovers the original upper point.

The construction uses Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach*, §§9.2.2–9.2.3 and 9.6, and the set form of Proposition 9.4.28.
