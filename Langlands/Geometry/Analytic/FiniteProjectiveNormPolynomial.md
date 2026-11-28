# Norm polynomial of a finite projective algebra

`Langlands.Analytic.exists_normPolynomial` takes a finite family \(b_i\) in a
commutative algebra \(S\) that is finite projective as a module over \(R\). It
constructs a multivariable polynomial over \(R\). For every \(R\)-algebra \(L\)
over which \(L\otimes_R S\) is identified with a finite product \(L^\iota\), the
polynomial specializes to the product of the linear forms
\(\sum_i b_i(j) X_i\) for \(j\in\iota\).

This is the determinant construction of the algebra norm of \(\sum_i b_i X_i\).
The proof splits \(S\) off a finite free \(R\)-module by a section \(s\) and a
retraction \(r\). It takes the determinant of the matrix of
\(1+s(\sum_i X_i m_{b_i}-1)r\), where \(m_{b_i}\) denotes multiplication by \(b_i\).
After base change, the matrix identity
`Matrix.det_one_add_mul_comm` and \(rs=1\) reduce the determinant to the one on the
split algebra. Its coordinate basis diagonalizes all the multiplication
operators, which gives the product formula. The proof permits an empty product
and varying rank on the base.
