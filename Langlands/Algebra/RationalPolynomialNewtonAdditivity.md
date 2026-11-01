# Additivity of the rational Newton transform

`Langlands.Algebra.RationalPolynomial.newtonPolynomialAddHom d` is the additive
homomorphism from rational sequences to rational polynomials whose value on `a`
is the existing Newton polynomial `newtonPolynomial a d`. It is defined for
every natural truncation `d` and every sequence. No vanishing of forward
differences or polynomiality hypothesis is imposed.

This is an internal construction from the published finite Newton formula.
Each iterated forward difference preserves addition, evaluation at zero
preserves addition, and division by the fixed factorial and multiplication by
the fixed falling factorial preserve addition. Finite summation therefore
preserves addition as well. The zero-sequence proof uses the existing lemma
that a vanishing forward difference remains zero at higher orders, starting
at order zero.

The companion theorems `newtonPolynomial_zero`, `newtonPolynomial_add`,
`newtonPolynomial_sub`, and `newtonPolynomial_sum` express the zero, binary
addition, subtraction, and finite-sum identities of this homomorphism.
They concern the constructed truncations themselves, including truncations
which do not reconstruct their input sequences.

The same contribution includes `Modules/CoherentEulerPolynomialAdditivity`,
which applies these numerical identities to actual coherent Euler sequences.
These identities support coherent-filtration arguments; they assert no
positive leading coefficient.
