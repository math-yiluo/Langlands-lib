# Actual dual L-polynomial data

`TemperedLFactorDual.DualTwoFamilyLPolynomialData` records a certified
L-polynomial for the actual inverse-transpose pullbacks of the two normalized
inductions, certified polynomials for every pair of inverse-transpose blocks,
and a normalized residual witnessing that their double product is divisible
by the induced polynomial. Certificates use the negated additive character
and the original supplied additive Haar measure. Field and both carrier
universes remain independent.

`nonempty_dualTwoFamilyLPolynomialData` constructs these data from full
Whittaker type of the two block families. It reverses both finite families,
takes their inverse-transpose pullbacks and obtains full Whittaker type at
the negated character using `isOfWhittakerType_firstDual`.
`DominantRankTransport.negatedSelfDualHaar` certifies that the supplied measure
is self-dual for that character without changing the measure. The constructor
then applies `TemperedLFactorDivisibility.twoFamilyLPolynomialData` to the
reversed dual families.

The published `Parabolic.normalizedProductInverseTranspose` equivalences
identify their actual normalized inductions with the pullbacks of the original
inductions. `IsPadicSymmetricLPolynomial.congr_equiv` transports both induced
certificates along these equivalences. Reversal surjectivity reindexes the
dependent block certificates; `Equiv.prod_comp Fin.revPerm` reindexes the two
finite polynomial products. The normalized residual and its factorization
are transported unchanged.

This is a derived internal construction from the named induction, Whittaker
and divisibility results. No additional literature assertion is introduced.
It supplies dual certificates and divisibility data; it does not assert a
pole bound, square-integrable genericity or the closed tempered product theorem.
