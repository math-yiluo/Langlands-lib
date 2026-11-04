# Uniform nilpotence from geometric nilpotence

Author: Worker 1487.

This internal derivation connects the published geometric-point predicate
`IsNilpotentGroupScheme` to the published all-test predicate
`HasUniformNilpotentPoints`. For a smooth connected affine group scheme over
any field, a single finite lower central bound works on every relative scheme
test, including nonreduced tests. All fields and groups remain at arbitrary
universe `u`.

`IsNilpotentGroupScheme.uniformNilpotenceBound` chooses such a natural number
from a proof of geometric nilpotence. Its specification states the uniform
lower central vanishing. The choice is not asserted to be the least bound.

The universal left-nested commutator word has an actual product scheme as
its source. If a later word is identically the unit, an earlier word value
lies in the appropriate upper central term of every group of points. This
follows by induction on the upper central index, using a pair of an earlier
word input and one more arbitrary group point. Applying this to the zeroth
word puts the entire point group in the bounded upper central term; Mathlib's
upper/lower central series equivalence gives the uniform lower central bound.

Geometric nilpotence gives a bound on the abstract group of points over the
algebraic closure. The actual pullback point equivalence reads those as points
of the original group on the geometric field test. Every universal word
value at that test lies in the bounded lower central term and therefore equals
the unit.

Each word source is geometrically reduced and locally of finite type, by the
published geometry of powers of smooth connected affine groups. After base
change to the algebraic closure, equality on rational points therefore implies
equality of morphisms: closed points have residue field equal to the base
field, closed points are dense, and the target is separated. Faithfully flat
base change reflects that equality. This proves that the bounded universal
word is identically the unit over the original field. The preceding upper
central argument then supplies the all-test uniform bound.

The argument uses existing definitions and geometric results; it introduces no
new literature translation or nilpotence convention. It does not construct a
central maximal torus or a unipotent quotient and does not prove the structural
central-torus theorem or the no-torus unipotence theorem.
