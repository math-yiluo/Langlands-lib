# Extending a coefficient action to the division order

`integerCyclicAddCoordinates` expresses the actual division order as the additive group of tuples of integral coefficients. The inverse sums the coefficients on the left of successive powers of the division uniformizer.

`liftCyclicOrder` takes a ring map from the embedded integer ring to a semiring and an element of the target satisfying the arithmetic conjugation and scalar power relations with that map. It constructs a ring map from the actual division order. The sum formula respects addition, and moving a power past a coefficient gives the product of two monomials. The scalar power relation reduces any monomial to one in the integral basis. The coefficient and uniformizer value lemmas show that the map extends the given data. The same integral expansion proves uniqueness.

This is the generators and relations construction derived from the presentation in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 B, printed p. 110.
