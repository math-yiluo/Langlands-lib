# The characteristic-p criterion from explicit structural inputs

This internal deduction assembles the central additive-subgroup criterion in
prime characteristic from two explicit proposition inputs:
`SeparablyClosedRationalPointStatement.{u,u}` and
`RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}`. It proves neither
input and does not complete the unrestricted all-field target.

`lineThroughVectorFactor` composes a map into a vector factor with its unit
inclusion into the product, the inverse of an actual group-scheme product
isomorphism, and a subgroup inclusion into the ambient group. The companion
lemmas prove closedness when the original map and subgroup inclusion are
closed and the complementary factor is separated, and centrality when the
subgroup inclusion is central.

For a smooth connected affine unipotent group with a nonconstant affine-line
map in characteristic `p`, the published pointed commutator and power
constructions give a smooth connected affine commutative central subgroup
killed by `p`. They retain a nontrivial family with every original group
parameter and with its entire basepoint section equal to one.

The supplied vector-factor proposition decomposes that subgroup as a vector
group times a complementary group whose affine-line maps become constant
over the separable closure. Affineness makes the complementary factor
separated. The pointed-family positive-dimension test, using the supplied
rational-point proposition, shows that the vector factor has positive
dimension. An actual closed coordinate line in this factor then gives the
central closed additive subgroup by the composite above. Its vector
coordinates are natural on every relative scheme test.

`criterion_of_charP` combines this construction with the existing unconditional
forward implication. The field is arbitrary within prime characteristic,
including finite and imperfect fields; the universe is arbitrary. Both
structural propositions remain arguments of the theorem. There is no claim
here of an unconditional criterion or of a characteristic-zero result, and
the published target and its imports are unchanged.
