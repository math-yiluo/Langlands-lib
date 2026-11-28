# Nilpotence and unique powers in the upper-unipotent group

For a matrix \(a\) in `GeneralLinear.upperUnipotent`, write \(a=1+A\),
with \(A\) strictly upper triangular. If \(A\) vanishes below the
\(m\)-th superdiagonal, multiplication on either side by a strictly
upper triangular matrix gives a matrix vanishing below the next
superdiagonal. In \(ab\) and \(ba\), the linear terms \(A+B\) agree and
the two quadratic terms therefore vanish on all those entries.
Multiplication by \(a^{-1}b^{-1}\) preserves that agreement.
Thus \([a,b]\) also vanishes below the next superdiagonal after subtracting
the identity. Induction puts matrices with this vanishing at the
corresponding term of the upper central series, proving
`upperUnipotent_isNilpotent` over a commutative ring.

For `upperUnipotent_pow_injective`, suppose two matrices agree below the
\(m\)-th superdiagonal. On the \(m\)-th superdiagonal the difference of
their \(e\)-th powers is \(e\) times the difference of the matrices.
Induction on \(e\) gives this formula from \(AB\), whose difference
at that level vanishes because the factors are strictly upper triangular.
If the \(e\)-th powers agree and \(e\) is nonzero in the field, induction
along the superdiagonals gives equality of the matrices. The
explicit root in `UpperUnipotentPowers` then gives
`upperUnipotentPowerEquiv`, the power map with the root as its inverse.
