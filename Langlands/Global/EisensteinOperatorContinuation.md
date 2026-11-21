# Continuing the operator tests of a finite Eisenstein family

`scalarAutomorphicOperator` uses a linear left inverse of the injective
scalar evaluation on finite-smooth rational functions. This extends each
concrete matrix operator to a linear map on scalar functions. On growth
vectors the extended scalar evaluation agrees with the continuous operator
test, so the formula there is independent of the choice of left inverse.

Fix a finite basis of continued Eisenstein functions, a concrete operator
for each basis vector, and a combination of the unoperated vectors whose
scalar coefficients are holomorphic on the entire parameter space. Suppose
the evaluated operator sum equals the varying combination on a nonempty
open set. The local meromorphic witnesses for the finite family give a
common denominator near each parameter. With that denominator, the two
expressions have holomorphic scalar numerators. For the operator sum,
this uses the continuous operator tests. For the varying combination,
it uses the finite sum of products of the holomorphic scalar coefficients
and the evaluated basis numerators.

At an adelic point the difference vanishes on the given open set. Its
one-dimensional scalar linear family has local holomorphic numerators,
so a nonzero regular value would supply an injective member in every
nonempty open set by meromorphic injectivity propagation. This forces the
difference to vanish on the regular set of the specialization ball. The
scalar identity theorem makes the two normalized expressions equal on
the whole ball.

This internal argument implements the comparison of normalized holomorphic
operator families in Langlands, *On the notion of an automorphic
representation* (1979), proof of Proposition 2, printed pp. 205–206
(Corvallis Part I PDF pp. 200–201).
