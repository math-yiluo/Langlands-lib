# Real internal conjugators for two-power unitary elements

Author: Worker 1655.

This internal construction refines two-power internal unitarization by
preserving entrywise reality of the conjugating matrices. It works over
an arbitrary-universe `RCLike` field.

`conjugateEntries` applies scalar conjugation to every matrix entry,
including the inverse matrix. This is a multiplicative map, as distinct
from the order-reversing matrix adjoint. It commutes with the adjoint and
preserves positive definiteness, since entrywise conjugation is transpose
of the adjoint and both operations preserve positive definiteness.

The positive square-root uniqueness argument shows that a positive
definite square root of an entrywise real matrix is itself entrywise real.
If scalar conjugation sends `g` to `g⁻¹` and `g²` is unitary, then
`g * star g = (star g * g)⁻¹`. Applying entrywise conjugation to
`star g * g` therefore fixes it.

`HasInternalRealUnitaryConjugate H g` asks for a matrix `c` in `H`, fixed
by entrywise scalar conjugation, such that `c * g * c⁻¹` is unitary.

`exists_real_positive_conjugator_of_square_unitary` proves this with a
positive definite conjugator when `H` is polynomially defined and stable
under adjoints, `g` lies in `H`, scalar conjugation inverts `g`, and `g²`
is unitary. Internal polar factors give `g = k * a` with `k` unitary and
`a` positive definite in `H`. Then `a² = star g * g`, which is entrywise
real by the preceding argument. Positive square-root uniqueness makes
`a` entrywise real. Choose a further internal positive square root `c`
of `a`; uniqueness makes `c` entrywise real as well.

As in the internal two-power construction, unitarity of `g²` and the
polar identity give `(k * a * k⁻¹)² = (a⁻¹)²`. Both roots are positive
definite, hence `k * a * k⁻¹ = a⁻¹`. Applying the same reasoning to `c`
gives `k * c * k⁻¹ = c⁻¹`, and group identities yield
`c * g * c⁻¹ = k`. Thus the conjugator has all required properties.

`exists_real_conjugator_of_two_power_unitary` proceeds by induction on
`r` when `g^(2^r)` is unitary. The induction hypothesis supplies an
entrywise real internal conjugator `b` for `g²`. Reality of `b` ensures
that entrywise conjugation still inverts `b * g * b⁻¹`. The square case
then supplies an entrywise real conjugator `a` for that element, and
the composite `a * b` remains entrywise real and in `H`. The base case
uses the identity conjugator.

`exists_real_conjugator_of_two_power_eq_one` specializes this result
to `g^(2^r) = 1`, since the identity matrix is unitary. No condition that
the order be exactly `2^r` is needed. Entrywise scalar conjugation need
not preserve all of `H`; only its stated action on `g` is assumed.

The provenance is this internal refinement of the published polar and
positive-root constructions, with the same positive-square uniqueness
argument as two-power unitarization. No external source is asserted.
The initial ambient star realization and actual real-scheme descent
remain outside this intermediate construction.
