# Signed determinants of Hermitian Gram matrices

`Form.signedDeterminant` is \((-1)^{\lfloor n/2\rfloor}\det H\) for the actual invertible Gram matrix \(H\) of a Hermitian form in dimension \(n\). It is nonzero and fixed by coefficient conjugation. This sign makes every hyperbolic plane contribute a unit signed determinant.

For an actual Gram matrix displaying several hyperbolic planes, `MultiHyperbolic.det_gram` gives the determinant of the middle block times \((-1)^{r}\), where \(r\) counts the planes. A simultaneous relabeling puts the middle matrix in a diagonal block and the planes in a permutation block. The permutation swaps the two ends of each plane, which gives the stated sign.

In dimension two, `Form.exists_isotropic_of_signedDeterminant` takes an element whose product with its conjugate equals the signed determinant and produces a nonzero isotropic vector. If the first diagonal entry vanishes, the first coordinate vector is isotropic. Otherwise, writing that entry as \(a\), the next entry of the first row as \(h\), and the norm witness as \(b\), the vector \(((b-h)/a,1)\) has self-pairing zero by the signed determinant identity.
