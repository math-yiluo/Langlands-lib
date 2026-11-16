# A quadratic fppf cover with an invertible root commutator coefficient

This internal construction adjoins a root of the monic polynomial
`X² - X - 1` over an arbitrary commutative ring. Its coefficient map is
faithfully flat and finitely presented, including when the original ring is
the zero ring. The root `t` is a unit with inverse `t - 1`, and satisfies
`t² - 1 = t`; in particular `t² - 1` is a unit. No characteristic is excluded.

The proof uses the free module structure on a quotient by a monic polynomial
and the faithful flatness of a nonzero free algebra. The zero ring is handled
separately by a bijective coefficient map. Evaluation of the defining equation
gives the unit and its inverse.

`exists_unit_test` applies this construction to the ring of global functions
of an affine test scheme. It produces an affine surjective flat locally
finitely presented refinement and transports the root to its global functions.
This is a preparatory input for the formula expressing a root-group point as
a commutator with a coroot value. This module proves only the construction
and its fppf properties, not that group-theoretic formula.
