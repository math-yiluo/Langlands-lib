# Rational lifting over finite fields

For any finite field `k : Type u`, the theorem
`HomogeneousQuotient.rational_lifts_pseudo_finiteField` lifts every rational
point of the supplied quotient under the original projection `q`.
Its inputs are an actual pseudo-parabolic inclusion `i : P ⟶ G`, an affine
ambient group, a smooth, surjective, quasi-compact projection, and the exact
right-coset fiber equivalence on every relative scheme. It retains the original
`Q`, `q`, subgroup predicate, and all-test fiber equivalence. No rational lift or
section is an input. Target separatedness and finite-type assumptions are not
needed for this finite-field result.

The construction `rationalLiftPseudoFiniteField` chooses an actual lift from
this existence theorem, and `rationalLiftPseudoFiniteField_comp` proves that
its composite with the supplied `q` is the input point. The choice is not
asserted to be canonical, natural, or a scheme morphism.

The proof is an internal assembly of published results. The pseudo-parabolic
structure proof supplies connectedness of this same `P` through
`IsPseudoParabolicSubgroup.source_connectedSpace`. The published
`finiteFieldTorsorPointStatement` supplies the finite-field torsor theorem.
The existing
`HomogeneousQuotient.rational_lifts_pseudo_of_finite_torsor_and_connected`
combines them: the exact quotient fiber is an actual torsor under `P`, its
finite-field point gives a point of `G`, and the rational-point equivalence
transports its image equation to the identity-test point convention. Smoothness
of `P` follows from the identity fiber of the smooth projection, and affineness
from its closed inclusion in `G`, as implemented in that existing adapter.

This module discharges the finite-field branch of the host all-field lifting
problem. It does not prove the infinite-field branch or the full published
`PseudoParabolicQuotientRationalLiftingStatement`.
