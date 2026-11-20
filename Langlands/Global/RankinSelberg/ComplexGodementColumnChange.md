# The column change of variables in the complex Godement Whittaker integral

`columnIntegral_eq` implements the change of variables \(u=hv\) in
the inner column integral of Jacquet's formula (7.6). The real
determinant of this complex-linear equivalence is
\(|\det h|_{\mathbb C}\), the squared modulus of \(\det h\).
Consequently the pushforward of the supplied additive product Haar
measure has factor \(|\det h|_{\mathbb C}^{-1}\). The character of the
last coordinate of \(v=h^{-1}u\) is the positive Fourier character at
frequency \(h^{-T}e_m\). The test in the resulting partial Fourier
integral is evaluated at the matrix with first block \(h\) and this
appended frequency column.

`integrable_column` proves absolute convergence of every inner
column integral when the original test is Schwartz. It restricts the
test to the affine column slice, whose inclusion has a lower norm
bound, and multiplies it by a character of unit modulus. The same
measure change transports this integrability to the original column
variable.

`complexGodementColumnChange` assumes a Schwartz representative of the
partial Fourier transform. The Jacobian shifts the exponent of the
normalized determinant from \(s\) to \(s-1\). The fixed-vector
Godement convergence theorem then gives absolute convergence of the
outer integral and entire dependence on \(s\).

The calculation implements Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), (7.6)–(7.7), p. 48. The construction of a Schwartz
representative of the partial transform and comparison with the
larger-rank Whittaker functional remain separate inputs.
