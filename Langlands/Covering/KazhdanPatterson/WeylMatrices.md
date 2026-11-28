# Type A Weyl representatives in the special linear group

For distinct indices \(a,b\) and \(x\in F^\times\), write \(T_{ab}(x)=I+xE_{ab}\). The matrix `rootWeylMatrix` is
\[
w_{ab}(x)=T_{ab}(x)T_{ba}(-x^{-1})T_{ab}(x).
\]
On the ordered pair of indices \(a,b\) its block is \(\left(\begin{smallmatrix}0&x\\-x^{-1}&0\end{smallmatrix}\right)\). Each remaining column is an identity column. Every factor is a determinant-one transvection. The proof of `toGL_rootWeylMatrix` uses the row update formulas for transvections to compute the column units of the monomial product. Multiplying by \(w_{ab}(-1)\) gives the coroot matrix with diagonal entries \(x\) at \(a\) and \(x^{-1}\) at \(b\), as in `toGL_rootWeylMatrix_mul_negOne`.

The simple matrix `simpleWeylMatrix` is \(w_{i,i+1}(-1)\). Its upper off-diagonal block entry is \(-1\), and its lower entry is \(1\). For each permutation \(w\) of the matrix indices, `weylReducedWord` chooses a shortest list of adjacent transpositions with product \(w\). Such a list exists by generation by adjacent transpositions and the least-number principle. `weylMatrix` evaluates that list in the simple matrices. It sends the identity to the identity and has permutation support \(w\). The latter follows by multiplying monomial matrices, with column units \(d(v(j))e(j)\) for the product of \((w,d)\) and \((v,e)\).

## Source

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §2, printed p. 141, PDF p. 11, minimal words and their matrix products. The signs and the two root formulas are those of §3, printed p. 146, PDF p. 16, immediately before the definition of the general linear cocycle. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
