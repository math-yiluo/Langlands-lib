# Weight vectors in represented dynamic subgroups over a ring

This is derived internal infrastructure for Task 6700. It extends the
field-base tangent-image argument in `Rational.StandardLeviLieWeights` to an
arbitrary commutative base and uses the published `dynamicRingLie` theorem.
It makes no additional external literature assertion.

The first lemma identifies membership in the image of the actual differential
of a represented subgroup with membership of the actual dual-number point in
that subgroup functor. Representability provides a lift of the point, and
monicity reflects reduction to the identity. This holds for any coefficient
algebra over any affine commutative base.

For a character of a commutative group scheme, restriction along a cocharacter
restricts its Lie weight. If the restricted character is the zeroth power
character, the arbitrary-ring dynamic Lie theorem puts the vector in the
represented centralizer. If it is a positive integral power, that theorem puts
the vector in the represented contracting subgroup. The exact character
composition equalities are hypotheses; they avoid any field-only character
lattice detection assumption.

Given an explicit torus factor through the centralizer, its actual differential
therefore identifies the two character weight spaces. Monicity reflects the
weight condition. The equivalence uses this differential, and its evaluation
formula records that compatibility. The final construction gives the unique
linear lift of the positive character weight into the actual Lie module of the
represented contracting subgroup, with a proved differential composition
identity.

All dynamic weight results retain an arbitrary commutative base in universe u.
They assume the ambient group is affine and locally of finite presentation and
the representative is affine. No reductivity, smoothness, connectedness,
reducedness, localness, field or nontrivial-base hypothesis is added.
