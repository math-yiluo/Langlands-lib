# Openness of logarithmic unit congruence subgroups

This derived supporting module starts with a positive scale `c` and the
normalized negative logarithm used by `logAdditiveValuation`. It proves that
`r ≤ negativeLogValue c a` is equivalent to `a ≤ exp(-c r)`, with the zero
value handled separately. The same logarithm vanishes exactly at value one.

For an ultrametric normed field, the scalar congruence subgroup is therefore
the inverse image under the field-unit value map of the intersection of the
unit sphere about zero and the closed ball of radius `exp(-c r)` about one.
Both are open in an ultrametric field; the radius is strictly positive.
Continuity of the unit value map proves openness at every nonnegative real
depth, including zero. The proof uses Mathlib logarithm inequalities and
ultrametric sphere and ball topology, without a completeness or discreteness
hypothesis. This module does not construct a centralizer filtration.
