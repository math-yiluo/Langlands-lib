# The geometric radical of a dynamic parabolic

`DynamicGeometricUnipotentRadicalStatement` is a proposition in every
universe over an arbitrary field. For a connected reductive group `G` and
a cocharacter `χ`, let `p : P → G` represent the actual dynamic parabolic
and let `r : U → P` have composite `r ≫ p` representing the actual dynamic
identity-limit subgroup. Both representation conditions are on every test
scheme. The representatives and the compatible inclusion are arbitrary.

The conclusion is exactly the predicate `IsGeometricUnipotentRadical r`
from `Rational.SemistandardIntersection`. It requires `r` to be a closed
subgroup, `U` to be smooth, connected and unipotent over the ground field,
and its range to be normal in `P`. After base change to the algebraic
closure it requires connectedness, unipotence and normality, and containment
of every smooth connected unipotent normal closed subgroup of the base
changed `P` in the range of the base changed `r`. Smoothness and closedness
after base change follow from their ground-field conditions. The geometric
maximality condition is part of the conclusion; it is not a hypothesis.

This statement is an internal structural proof obligation extracted from
`DynamicSemistandardIntersectionStatement`: after lifting the second
cocharacter into the first centralizer, the dynamic subgroup comparisons
reduce its geometric radical clause to this theorem. The statement does
not assert a general quotient or scheme-theoretic image construction and
does not replace geometric maximality by the normality or complement law
on points. It assumes no nesting, split ambient group, perfect field or
characteristic restriction.

The provenance is the precise existing dynamic subgroup and geometric
radical predicates and the structural clause of the semistandard target.
This extraction adds no independent external citation or claimed proof.
The module defines a proof target; it does not prove it. Dynamic
smoothness, connectedness, unipotence and the maximality argument remain
obligations of its proof.
