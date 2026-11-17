# Cyclic polynomial coordinates over arbitrary coefficient rings

This derived module extends the polynomial-cutoff argument in the Library's
`Rational/CyclicWeightCoordinates` from fields to arbitrary commutative coefficient
rings. It does not assert existence of polynomial coordinates over such a ring.

For a group-valued algebra functor corepresented by an algebra B, with a split-torus
action and nonzero character a, `CyclicPolynomialCoordinates` records finitely many
homogeneous generators of B modulo the ideal defining its first intrinsic cyclic
weight subgroup. Their weights are positive integral multiples of a. The evaluation
map from the corresponding polynomial algebra is required to be surjective; an
isomorphism is not required.

`mem_iff` proves, for every algebra A over the coefficient ring and every A-point
of the first cutoff, that membership in cutoff r is equivalent to vanishing of
all the supplied coordinates of weight less than r. In particular, this statement
does not restrict A to fields or reduced rings.

The proof lifts each homogeneous quotient generator to a homogeneous component in
B. The forward implication uses the defining weight-component equations. For the
reverse implication, the quotient algebra is graded by natural multiples of a;
surjectivity expresses a homogeneous component as a polynomial in the supplied
generators. The Library's commutative-ring `decompose_aeval` theorem extracts its
weighted homogeneous part. Every positive-degree monomial of degree less than r
then contains a coordinate required to vanish. The auxiliary lifting and
low-degree evaluation proofs use no field property.

`conjugate` is the actual conjugated point of the first cutoff when the conjugator's
twisted orbit is constant. `conjugate_low_coordinates` proves preservation of every
supported-coordinate cutoff, by the arbitrary-ring intrinsic weight-subgroup
conjugation theorem in `Rational/CyclicWeightConjugation`. This is an algebra-point
result; identifying it with a particular root chart, or proving compatibility
under a change of maximal torus, remains a separate obligation for Task 7200.
