# The Kazhdan–Patterson bilinear pairing on the diagonal torus

The diagonal torus is written in ordered coordinates \(t=(t_1,\ldots,t_r)\) with each entry in the commutative group \(U\). `Langlands.KazhdanPatterson.diagonalDeterminant` is the product of the entries. For \(U=F^\times\), `determinant_diagonalUnits` identifies this product with the determinant of the actual diagonal matrix in \(\mathrm{GL}_r(F)\) by applying the determinant formula for a diagonal matrix.

For a bilinear pairing \(H:U\times U\to A\) into a commutative group \(A\), `torusPairing` is the pairing

\[
(t,s)\longmapsto
\prod_{i<j} H(t_i,s_j)\,
H\!\left(\prod_i t_i,\prod_j s_j\right)^c.
\]

Each factor is the pullback of \(H\) by two coordinate evaluations. The determinant factor uses the two determinant homomorphisms and the \(c\)-th power in \(A\). The pointwise product and power of homomorphisms establish multiplicativity in both variables. The lemma `torusPairing_apply` evaluates these homomorphisms to give the displayed formula.

For \(U=F^\times\) and \(H\) the degree-\(n\) Hilbert symbol, the ordered product is the cocycle on the diagonal torus in Kazhdan–Patterson. The determinant factor is the restriction of their \(c\)-twist. Banks–Levy–Sepanski obtain the same untwisted product using the inverse of \(H\) for their Steinberg symbol.

## Sources

- Kazhdan and Patterson, *Metaplectic forms*, §0.1, printed pp. 39 and 41, PDF pp. 6 and 8, diagonal cocycle and determinant twist. Literature ID `kazhdan-patterson-1984-metaplectic-forms`, SHA-256 `0f91142e8fc3814981fb77e3a3f05a7359ebd4a5e9afdf5386eb357cb4f2b57e`. [DOI](https://doi.org/10.1007/BF02698770)
- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §3, Lemma 1, printed p. 146, PDF p. 16, inverse-symbol product on the diagonal torus. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
