# Holomorphic division by a polynomial with varying roots

`MovingRootDivisionStatement` concerns a jointly holomorphic function \(F(z,s)\)
on a disk about \(z=0\) times the full \(s\)-plane. A finite list of holomorphic
functions \(r_j(z)\) specifies the divisor \(\prod_j (s-r_j(z))\). Suppose at
parameters accumulating to the center the entire spectral slice of \(F\)
is the divisor times an entire function. Then \(F\) is the divisor times a
jointly holomorphic function on the whole product domain. The divisor keeps
every entry of the list, including repeated roots and roots that meet at a
particular parameter.

The proof fixes a spectral center and takes a smaller parameter disk
containing zero and the parameter under consideration. The roots are bounded
on the closure of that disk. A single sufficiently large circle in the
spectral variable therefore avoids all roots for parameters in the smaller
disk and spectral centers near the chosen one. The circle average of the
quotient is holomorphic in both variables there by
`differentiableOn_circleDivision`.

At the accumulating parameters the mean value property identifies the
circle average with the supplied entire quotient. The identity theorem in
the parameter variable gives the multiplied-out equality throughout the
smaller disk. The quotient defined by the punctured spectral limit agrees
with these local circle averages. Each finite product is nonzero in a
sufficiently small punctured neighborhood of any fixed spectral argument,
so this agreement follows by cancellation and continuity of the local
quotient.

This is a derived analytic step for the passage from position characters
to real blocks in Jacquet's *Archimedean Rankin–Selberg Integrals*,
Proposition 11.1, author p. 82. It permits cancellation of the polynomial
in the pair denominator once cancellation holds on a set of inducing
parameters with a limit point.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
