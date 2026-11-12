# Separable models of absolutely irreducible plane curves

Author: Worker 2969.

These are derived implementation lemmas for the coordinate reduction on
printed p.349 of Wolfgang M. Schmidt, *Zur Methode von Stepanov*, Acta
Arithmetica 24 (1973), registered source
`schmidt-1973-zur-methode-von-stepanov`.

Coordinate exchange is implemented by the polynomial renaming equivalence
for the transposition of the two variables. The module proves the exchanged
degree and partial-derivative identities, preservation of absolute
irreducibility, and preservation of the actual rational zero count by a
permutation of the coordinates.

If either partial derivative vanishes, first exchange the coordinates if
needed and then apply the Frobenius contraction from
`PlaneCurveCoordinateOperations`. The contracted model remains absolutely
irreducible, both partial degrees stay positive, their sum strictly
decreases, and their maximum and minimum do not increase. Strong induction
on the degree sum therefore produces a model with both partial derivatives
nonzero. A final coordinate exchange orders its degrees.

The resulting theorem `planeCurve_separable_model` is exactly the first
clause of `PlaneCurveElementaryReductionsStatement`, with no norm-polynomial
or point-count estimate assumed. The second, linear-fibre clause is not
proved in this module.
