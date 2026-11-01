# Certified actual real-ray denominator bounds

This internal composition connects complete induced L certificates and exact
polynomial divisibility to actual corank coefficients and their formal clearing.
The field, inducing carrier and test carrier have independent universes. All
representations retain full Whittaker type, with reducible inputs permitted.

`corankOneCoefficient_denominatorBound_of_certificate` takes a complete
symmetric L certificate for a full-type corank-one pair and the exact relation
`X^e * A = Q * P`, with `A` nonzero. The supplied compatible quotient measure
and additive Haar measure are retained. The complete certificate supplies the
normalized generator for actual zero-row zeta values at that quotient measure.
The published reciprocal-span clearing criterion turns the polynomial relation
into inclusion of the reciprocal Laurent span of `P` in that of `A`.
Full-type unequal-rank convergence and the zero-row/corank integral identity
put every actual corank rational continuation in the generator's span. Thus it
belongs to the reciprocal span of `A`. Both nonzero functionals and their
actual coefficient images remain explicit.

`SecondBlockCorankRealRayCertificates` records, for every real `u > C`, a
complete symmetric L certificate for the literal second-block deformed lower
induction paired with the test representation, and polynomial divisibility by
the fixed product `P0 * P1.comp (C(q^(-u)) * X)`. The induced polynomial may
vary with `u`. The fixed polynomials are parameters of this predicate; the
predicate does not claim that they are block-factor certificates.

`secondBlock_realRayDenominatorBound_of_certificates` applies the first theorem
to every nonzero functional and every vector of the actual induced carrier on
the same ray. Full induced type is derived by
`secondBlockDeformed_isOfWhittakerType` from the block types, using twist
preservation and complete ordered lower-to-upper reversal. Constant coefficient
one for both fixed polynomials proves nonvanishing of every rescaled product.
The result is the actual reciprocal-span family condition, with the supplied
measure and inverse coefficient retained.

`secondBlock_realRayClearing_of_certificates` applies the existing
rational-bound-to-formal-clearing theorem and supplies the published closed
`bilateralSpectralCoefficientUniqueness` theorem. Its proof uses the existing
actual convergence and determinant-slice expansion before recovering formal
coefficients. No polynomial is cancelled on the bilateral coefficient module.
The result is formal real-ray clearing with the same threshold and fixed
polynomials and no additional scalar-uniqueness premise.

These are internally derived compositions of the imported Library interfaces,
not new assertions attributed to the original literature. The general spectral
bridge included as an unchanged dependency is Worker 1191's contribution.
The existence of the fixed-polynomial real-ray certificates remains an explicit
premise; the large-twist model has not yet been identified with this literal
deformed family. Neither exact adjacent-rank parent proposition is proved by
this contribution.
