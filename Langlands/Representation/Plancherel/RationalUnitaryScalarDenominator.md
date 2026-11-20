# A single denominator for a unitary-regular scalar

`UnitaryRegularScalarPresentation.ofUnitaryRegular` starts with a fraction
in the actual unramified function field that is algebraically regular at
every unitary character. It returns a numerator and one denominator
nonzero at every unitary character. The output satisfies an equality by
cross-multiplication in the regular-function algebra with the supplied
fraction.

Choose a reduced numerator and denominator in the Laurent unique
factorization domain. At each unitary point the definition of regularity
supplies a local numerator and denominator. Cross-multiplication in the
field, followed by injectivity of the regular algebra, gives an equality in
that algebra. Relative primality makes the reduced denominator divide the
local denominator, so nonvanishing of the local denominator at that point
forces nonvanishing of the reduced one.

This is a derived algebraic conversion for inserting a unitary-regular
inverse scalar into the compact comparison in Waldspurger (2003), V.3
formula (1), printed p. 295 / PDF p. 61 (`waldspurger-2003-plancherel`).
Regularity of the scalar is a hypothesis.
