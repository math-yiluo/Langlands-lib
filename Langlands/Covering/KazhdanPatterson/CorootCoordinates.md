# Simple coroot coordinates on the special linear diagonal torus

Let \(F\) be a field. In \(\mathrm{SL}_{r+1}(F)\) the simple coroot \(h_i(x)\) has entries \(x,x^{-1}\) in adjacent positions \(i,i+1\) and ones elsewhere. The diagonal subgroup is parametrized by \((F^\times)^r\) through the product of these simple coroots. With indices starting at zero, the simple coroot parameter of a determinant-one tuple \(t\) at label \(i\) is \(x_i=\prod_{j=0}^i t_j\).

`simpleCorootCoordinates` gives the multiplicative equivalence from determinant-one tuples to simple coroot parameters in any commutative group. Its inverse adjoins an initial and a final one to the list of parameters and takes successive ratios. The proof uses the partial product recurrence and its inverse. For a parameter supported at a single index, the two nontrivial adjacent entries give `simpleCorootCoordinates_symm_mulSingle`. Applying the inverse homomorphism to the decomposition into single-coordinate tuples gives `simpleCorootCoordinates_symm_eq_prod`.

`slDiagonalMatrix` builds the actual matrix by applying `Matrix.diagonal` to the unit entries. Its determinant is the product of those entries. Conversely, a diagonal special linear matrix has nonzero entries on the diagonal because their product is one. `slDiagonalCorootEquiv` therefore identifies the tuple of simple coroot parameters with the diagonal subgroup of \(\mathrm{SL}_{r+1}(F)\).

## Source

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §2, printed pp. 140–141, PDF pp. 10–11, adjoining simple torus generators in their fixed order and the unique product expression at the start of p. 141. The adjacent coroots specialize to type A using the coordinate roots and simple roots of §3, printed p. 145, PDF p. 15. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
