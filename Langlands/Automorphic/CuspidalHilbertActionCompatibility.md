# The original finite and compact actions inside the full adelic Hilbert action

`CuspidalHilbertActionCompatibilityStatement` retains the full smooth scalar
coefficient premise, an arbitrary-universe number field with compact
`AdeleQuotient`, an actual cuspidal realization of `GL_(r+1)`, its prescribed
unitary central character, and a supplied full positive form `b` whose inner
product is the exact canonical determinant-band integral. It states that the
constructed `adelicHilbertRepresentation` restricts to the originally supplied
completed finite and standard compact actions on the same original Hilbert
completion. `cuspidalHilbertActionCompatibility` proves this statement.

The generic predicate `AgreesWithIsometries U φ B` is the equation
`U(φ(d))x = B(d)x` for every completed vector. The form-level predicate
`OperatorUnitaryFormCore.BoundedActionCompatibility b U φG φK` is the conjunction
of this agreement with `b.completedFiniteOperator` through `φG`, and with
`b.completedCompactOperator` through `φK`. In the actual statement these maps are
the finite adelic inclusion and the infinite inclusion of the actual standard
compact subgroup, respectively. These explicit Prop-valued predicates retain
the original operators and the original form completion.

The actual algebraic lemmas identify the translated band `L²` vector of a finite
or compact translation with the band vector of the original finite or compact
source operator. Their proofs use the pointwise faithful-descent identities
`toQuotient_finite` and `toQuotient_compact`, and the almost-everywhere values of
the prescribed `Lp` representatives. They do not change the band measure or
replace the source functions.

The generic dense-carrier argument uses the exact target values of the full
action, agreement of every translated embedding on the canonical dense carrier,
and injectivity of the identity isometry. These identify the two completed
operators on the dense carrier. Since both operators are continuous, their
equality holds on the entire completion. The two comparisons are packaged at
the generic positive-form level before actual specialization; this avoids
repeated reductions through the nested actual automorphic carriers without
changing the equations being proved.

The provenance is internal composition of the actual quotient translation and
completed-action constructions with dense extension uniqueness. No new external
theorem is claimed. The scalar coefficient premise remains unproved. No bounded
extension of a Lie operator, differentiable smooth-vector or genuine generator
comparison, derivative density, Whittaker uniqueness or unconditional cuspidal
operator multiplicity one is asserted.
