# Orders of unitary spectral gamma expressions

This derived helper uses the actual determinant Euler polynomials of supplied
endomorphisms on finite-dimensional complex carriers. The carrier universes of
the two endomorphisms are independent.

`operatorSpectralGamma` is epsilon times the Euler denominator at `s`, divided
by the second Euler denominator at `1-s`. It is meromorphic wherever epsilon
is analytic. If both operators preserve supplied positive definite Hermitian
forms, `q > 1`, epsilon is analytic and nonzero at `s`, and `Re(s)` is nonzero,
its order is nonpositive.

The proof first transports the nonpositive reciprocal order through reflection.
The map `s ↦ 1-s` is analytic with derivative `-1`, so it preserves order at
the corresponding point. At nonzero real part the first Euler denominator is
nonzero by positive-form preservation. Its product with epsilon is therefore
an analytic unit. Removing this unit leaves exactly the reflected reciprocal,
whose order is nonpositive.

`WeilDeligne.spectralGammaExpression` specializes this construction to the
actual inertia-fixed monodromy-kernel operator of a supplied Weil–Deligne
parameter and that of its algebraic dual. Underlying unitarity passes to the
dual and to the actual kernel invariant subspaces. No replacement operator or
carrier model is used. Consequently a positive order at a real point forces
that point to be zero when epsilon is an analytic unit on the real line.

The epsilon function and its analytic-unit property are explicit inputs.
This module asserts no local-constant-system existence, epsilon formula,
arithmetic/automorphic gamma identity, automorphic positive-form existence,
or proof of the full associated-pair induction proposition.
