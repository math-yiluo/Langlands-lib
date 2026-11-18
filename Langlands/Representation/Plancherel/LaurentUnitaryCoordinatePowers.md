# Cancellation of unitary coordinate pole multiplicities

This derived unit completes scalar coordinate multiplicity cancellation for
the elementary part of the argument used in Waldspurger (2003), V.2.3, printed
p.294 / PDF p.60, and Lemma V.3.1, printed p.295 / PDF p.61. The registered
original is `waldspurger-2003-plancherel`. It imports
`LaurentUnitaryBoundedCancellation` and its coordinate divisibility dependency.

`norm_le_of_dense` extends a norm inequality from a dense subset using
continuity and the closedness of its sublevel set.
`finiteLaurent_unitary_dense_nonzero` proves that a nonzero finite Laurent
polynomial has dense nonvanishing locus on the whole unitary torus: otherwise
it vanishes on a nonempty open piece, contradicting the unitary identity
theorem. The zero-dimensional torus is included.

`finiteLaurentCoordinateRoot_eval_cons` checks that the chosen coordinate root
evaluates as `z₀ - a`. `finiteLaurentCoordinateRoot_ne_zero` checks it is
nonzero when `a` is on the circle, evaluating at `-a` in the first coordinate.

`finiteLaurent_unitary_bound_cancel_factor` assumes a norm inequality on the
whole unitary torus for a numerator and denominator multiplied by a common
nonzero Laurent polynomial. On the dense locus where the common factor is
nonzero, the proof cancels its positive norm. Continuity then extends the
same inequality to the entire torus.

`finiteLaurentCoordinateRoot_pow_dvd_of_dense_unitary_bound` states that if
`(X₀ - a)^k` divides a Laurent denominator and the cleared numerator inequality
holds with a fixed real bound on a dense unitary set, the same power divides
the numerator. The point `a` lies on the circle, and the power `k` is supplied
before applying the criterion to any numerator.

The proof first extends the original inequality to the entire torus. It
inducts on `k`, uses the imported one-factor divisibility theorem, cancels the
common factor from the inequality, and applies the induction hypothesis to
the two remaining quotients. It does not assign a quotient value at any pole.

`finiteLaurentCoordinatePowerQuotient` constructs the resulting Laurent
polynomial quotient from the proved divisibility criterion, with the same
circle point, power, numerator, denominator, dense set and norm-bound data.
`finiteLaurentCoordinatePowerQuotient_spec` proves the exact polynomial
identity `p = (X₀ - a)^k * quotient`. The construction is a polynomial
quotient; it does not define a rational function at its original poles.

This result retains scalar multiplicities. It does not establish the actual
tensor's root-pole support or generic norm identity, change coordinates for
actual root characters, or construct a single canceled operator denominator
and its vector-valued polynomial numerator. Those remain separate obligations.
