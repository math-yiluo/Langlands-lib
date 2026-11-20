# Diagonal phases in complex Godement integration

`complexDiagonalKernel` evaluates the triangular Godement kernel on a
complex diagonal. Multiplying each diagonal entry by a phase and
multiplying the strictly upper entries in the same row by that phase
left multiplies the triangular matrix by a diagonal unitary matrix.
The character weight of the diagonal and the Borel covariance of the
smaller standard vector combine to move this unitary matrix onto the
compact variable.

For a continuous test the row phase changes preserve additive Lebesgue
measure on the strictly upper coordinates. The supplied right invariant
unitary measure is preserved by the compact translation. Consequently
these two integrations of the weighted kernel depend only on the
positive diagonal moduli. The same argument applies to the nonnegative
integral of the kernel's norm. This gives the phase change used to pass
to complex multiplicative diagonal variables in Jacquet's Tate
reduction.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, proof of Proposition 7.1, p. 44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
