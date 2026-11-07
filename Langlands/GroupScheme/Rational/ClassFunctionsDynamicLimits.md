# The canonical class quotient is constant along cocharacter limits

Author: Worker 1741.

This internal helper works with the actual canonical quotient `ClassFunctions.rho`
of an arbitrary affine group scheme over a field `K : Type u`. It imposes no
connectedness, reductivity, smoothness, perfection or infinitude hypothesis.
Every test scheme over `Spec K` is allowed, including nonreduced tests.

`rho_cocharacter_invariant` restricts the already proved all-test conjugation
invariance of `rho` to an actual cocharacter. `rho_eq_of_hasLimit` says that any
actual extension of that cocharacter's conjugation orbit to the affine line has
the same quotient value at zero as at its original point. Its proof applies the
published invariant-morphism limit theorem in `Dynamic.ActionUniqueness`; the
target is separated because it is the relative spectrum of the invariant
algebra. The comparison in `Dynamic.ActionConjugation` identifies that theorem's
abstract-action limit with the published cocharacter limit.

`rho_limit` specializes this equality to the chosen limit of a point in the
dynamic parabolic. It uses separatedness of the source only because the chosen
dynamic limit API assumes it. No existence of a parabolic containing a given
point, separation of torus conjugacy classes or geometric conjugacy in quotient
fibres is asserted here.

Provenance: internal derivation from the published canonical quotient and
dynamic-action uniqueness theorems. This helper does not invoke a new external
mathematical assertion.
