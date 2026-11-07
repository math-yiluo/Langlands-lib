# Actual-component reflected gamma product

`componentGammaProduct` proves the unchanged internal proposition
`ComponentGammaProductStatement`, with independent field, block-carrier and
component-carrier universes.

First the proof uses `normalizedProductWhittakerType` to obtain full Whittaker
type of the two canonical normalized inductions. Their admissibility contains
the ambient smoothness needed by `componentFactorComparison`. It extracts an
epsilon certificate for the supplied component pair, and one for each block
pair, from the closed Whittaker-type construction input.

`TemperedLFactorGamma.gamma_doubleProduct` supplies gamma factors of all block
pairs and certifies their product on the two inductions. The canonical
`symmetricGammaExpression` rewrites each block factor using its supplied
original and actual inverse-transpose L-polynomials. The same expression,
applied in the reverse direction, certifies the component epsilon-times-ratio
expression as a gamma factor of the component pair. Actual-component gamma
comparison identifies this expression with the induced product. This step
uses the actual subquotient hypotheses and ambient smoothness; it requires no
ambient L-polynomial certificate.

The finite-product identity for rational gamma expressions then packages the
rectangular product as one expression. Cancelling the product epsilon monomial
with `reflectedRatio_of_gammaExpression_eq` yields `ReflectedRatioData`. Its
coefficient is the component epsilon unit divided by the product of the block
epsilon units, and its exponent is the corresponding difference of epsilon
exponents. All dual certificates use the negated additive character and the
unchanged underlying Haar measure, as in the statement.

This is an internal combination of the cited published Lean theorems. It does
not prove component Whittaker type, existence of the supplied L-polynomials, or
the host JPSS (8.2) component product formula.
