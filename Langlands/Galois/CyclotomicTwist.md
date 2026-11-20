# Integral cyclotomic twists of actual Galois representations

This internal construction implements arithmetic weight changes in the
comparison of pure weakly associated families. A continuous unit-valued
character twists the existing action by scalar multiplication on the
same vector space. Continuity follows in the module topology on
endomorphisms. An invertible linear map intertwining two representations
twisted by the same character also intertwines the original actions,
by cancellation of its unit value at each group element. At a finite
place the same cancellation uses the pullback of the character along the
actual Galois restriction.

To compute the Euler polynomial after a twist, choose a finite basis
and use the determinant expression for the Euler polynomial. Substituting
the character value times the variable is a polynomial ring map. It
commutes with the determinant and leaves constant coefficients fixed,
so it has the same effect as multiplying the action by the character.

For an integral exponent \(k\), `geometricCyclotomicPower` raises the
inverse of the actual cyclotomic character to \(k\) and transports the
unit to the coefficients along a map from \(\mathbf Q_p\). A
continuous coefficient map makes the resulting scalar character
continuous. At every place of residue characteristic different from
\(p\), the character is trivial on inertia and equals \(q^k\) on any
geometric Frobenius lift, where \(q\) is the residue cardinality. This
gives the Euler-polynomial substitution at such places. For a coefficient
completion the construction uses its continuous map from \(\mathbf Q_p\),
with \(p\) the prime below the coefficient place. The residue field at
that coefficient place has characteristic \(p\).
