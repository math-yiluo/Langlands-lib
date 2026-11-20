# Monic polynomial approximation over a number field

`Langlands.Global.NumberFieldPolynomialApproximationStatement` gives a number-field polynomial that approximates prescribed monic polynomials in finitely many finite completions and all infinite completions. The local polynomials have a common positive degree and the constant term is the image of a fixed element of the number field at every specified place. The approximating polynomial has this degree and constant term.

The construction uses weak approximation in the actual completions to choose the intermediate coefficients. It sets the leading coefficient to one and the constant coefficient to the prescribed element. Coefficients above the specified degree vanish on both sides, so the approximation bounds hold for every coefficient.
