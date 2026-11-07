# Integral units with prescribed actual residue

For an actual embedded field `ι : L →ₐ[K] D` whose actual residue map
is surjective, `localDivisionSubfieldIntegerUnitLift` chooses an integral
unit in that field with the same actual division-algebra residue as a
given original integral unit of `D`. The field universe is independent
of the common universe of the local base field and division algebra.
No degree, Galois or cyclicity hypothesis is used.

The existence proof first lifts the residue along the surjective residue
map and then along the original field-integer reduction map. The
resulting integral element has nonzero residue, since its image is the
residue of a unit. The actual residue criterion then gives valuation
one and hence an actual integer-ring unit.
`localDivisionSubfieldIntegerUnitLift_spec` records the chosen unit's
exact residue equality.

This is an internal deduction from the published quotient and
integer-unit criteria. It supplies a concrete choice used in the
commutator movement construction and asserts no further source theorem.
