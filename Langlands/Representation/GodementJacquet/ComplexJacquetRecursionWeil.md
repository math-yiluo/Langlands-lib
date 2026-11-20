# Weil integration of the last-column Fourier kernel

With \(m=r+1\) and \(n=m+1\), split a complex \(m\times n\) matrix into
its first \(m\) columns and its last column. The operator
`complexLastColumnFourier` integrates in the last column against the trace
character and its self-dual measure. Using \(k=h^{-1}\), the frequency
\(h^\iota e_m\) in Jacquet's formula (7.7) becomes the last row of \(k\)
viewed as a column.

For each \(k\), the left-unipotent average of
`complexJacquetRecursionGroupKernel` is the integrand in the iterated
quotient expression. Inverting the unipotent variable changes its
simple-root phase to the character of \(W\). The column change
\(z\mapsto k^{-1}z\) turns the last-entry phase into the pairing with the
last row of \(k\). Its Jacobian shifts the exponent on \(k^{-1}\) from
\(n/2\) to \(n/2-1\). The unipotent determinant is one, and left
unipotent multiplication preserves the last row of \(k\).

`complexJacquetRecursion_eq_integral_group` applies the Weil integration
formula for the supplied compatible measures to this orbit identity.
It assumes the opposite factors in the orbit transform by inverse
characters, through the stated Whittaker law for \(W\), and that the
single-group kernel is integrable. The output identifies (7.7) and (7.8)
with the same quotient normalization and the parameter \(-a\) in the
primal Fourier phase.

Source: H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
printed and PDF pp. 48 and 50, formulas (7.7) and (7.8).
