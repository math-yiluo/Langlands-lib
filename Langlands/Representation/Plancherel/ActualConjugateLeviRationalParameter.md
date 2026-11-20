# Rational parameter transport of the actual standard tensor

Waldspurger IV.1 uses one regular denominator for the whole compact operator.
V.3 formula (1) evaluates the two standard factors after conjugating the inducing
parameter. This module implements that change of parameters for the fixed compact
standard tensor on the target side.

`IsPolynomialOn.parameterPullback` keeps the finite vectors of a numerator and
pulls every scalar coefficient back through the actual regular-function algebra
isomorphism. The evaluation identity for that isomorphism proves the formula
over the full rational-character parameter space. `parameterPullback_clears`
therefore pulls back the same denominator for every input vector.
`IsRationalOperatorOn.parameterPullback` also transfers its nonvanishing to the
whole preimage of the specified locus.

`pulledBackStandardTensor` uses the exact simultaneous locus of the particular
continued forward and reverse-dual standard operators. It reads the actual
same-Levi compact tensor through `ActualConjugateLeviTensor.genericParameter`.
Its rationality theorem invokes the existing `compactComparison_rational`
with the specified `ScalarInverseData`. This data exposes the remaining analytic
scalar composition witness for the actual reverse inverse. The separate left
translation factor acts before this tensor in the full comparison.

Source locators are Waldspurger (2003), IV.1 printed pp. 276–277/PDF pp. 42–43
and V.3 formula (1) printed p. 295/PDF p. 61.
