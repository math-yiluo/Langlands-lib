# Entire coefficients of the actual adjacent dual family

This internal construction supplies the dual half of the coefficientwise entire
continuation used in the adjacent-rank argument. It composes the published
corank determinant-slice theorem with the actual Weyl–inverse-transpose
transform, the block Weyl right translation, and the inverse-transpose
coefficient model of the fixed test representation.

`HasCommonCompactOpenRightLevel.translate` conjugates the given right level by
the fixed translation. `HasCommonCompactOpenRightLevel.firstDual` pulls the
given level back through the continuous inverse-transpose group automorphism.
Both operations retain openness and compactness using the corresponding
homeomorphisms.

`adjacentRankDualWhittakerFamily` uses precisely the translated first dual
function in the adjacent functional equation. Its values at any fixed group
element are evaluations of the original family at a fixed transformed element,
so their entire dependence is unchanged.

`adjacentRankDualCoefficientFamily` is the literal determinant-slice integral
coefficient of this family against `secondDualFunction` of the original fixed
test vector. The integrability and entireness theorem uses the actual
`secondDualModelMap` vector for the inverse-transpose pullback of the test
representation, with `secondDualFunctional`. Full Whittaker type of this test
is transported by the published inverse-transpose theorem. The original
compatible quotient measure is retained.

The result does not assert a gamma identity or a continuation of a functional
equation. It supplies integral analyticity needed for that next step. Its
provenance is internal composition of the named published constructions; it
does not state an additional theorem from the literature.
