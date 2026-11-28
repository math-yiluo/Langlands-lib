# Diagonal and Weyl coordinates of special linear monomials

The equivalence `slMonomialWeylEquiv` sends a determinant-one diagonal \(t\) and a permutation \(w\) to \(t\,\eta_w\), where \(\eta_w\) is `weylMatrix w`. The target consists of the monomial matrices in the actual special linear group. Each column has one nonzero entry, in row \(w(j)\) for column \(j\). These entries determine the permutation. Given two such products with the same matrix, the permutations therefore agree and right cancellation gives equality of the diagonals.

For surjectivity, write the column units of the given monomial matrix \(m\) and its representative \(\eta_w\) as \(d_j\) and \(e_j\). Their quotient \(m\eta_w^{-1}\) is the diagonal with entries \(d_{w^{-1}(i)}e_{w^{-1}(i)}^{-1}\) in row \(i\). It belongs to `slDiagonalTorus` because the two factors have determinant one. The inverse sends the identity matrix to the pair of identities.

## Source

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §2, printed p. 141, PDF p. 11, decomposition of the torus normalizer by its Weyl representatives and Lemma 2(c). The type A monomial description is in §3, printed p. 145, PDF p. 15. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
