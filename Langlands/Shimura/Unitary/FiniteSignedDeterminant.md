# Signed Gram determinants and norms at nonsplit finite places

Let \(K/E\) be a totally complex quadratic extension of a totally real number field with independent field universes. At a nonsplit finite place \(p\), the unique upper completion is quadratic over \(E_p\). Its nonidentity automorphism is the transported CM conjugation. The field norm after inclusion in the upper completion is therefore \(\bar z z\), and the fixed elements are the image of \(E_p\).

For a supplied central simple unitary algebra of degree \(n>1\) whose upper completed Brauer invariants at \(p\) vanish, `nonsplitSignedDeterminant` gives a unit of \(E_p\) together with the equation identifying its image with \((-1)^{\lfloor n/2\rfloor}\det H\) in the chosen Hermitian matrix chart. Taking determinants of the self-adjointness identity shows that this signed determinant is fixed by coefficient conjugation. Invertibility of the Gram matrix gives a nonzero scalar in the completed base.

`nonsplitCompletion_mul_mem_normSubgroup` shows that the product of two units with the same norm membership status is a norm. The local Artin map has kernel the actual norm subgroup and takes values in the group of order two of the quadratic completion. Equal membership status gives either two identities or two copies of the nonidentity automorphism, whose product is the identity.
