# The closed subgroup for real rank raising

For leading size \(r+1\), set \(a(h)=\operatorname{diag}(\det h,1,\ldots,1)\) for the invertible one-dimensional trailing block \(h\). The matrices

\[
u(x,h)=\begin{pmatrix} a(h)^{-1}&0\\x&h\end{pmatrix}
\]

form `rankRaisingSubgroup r`. The product has coordinates \((x a(k)^{-1}+h y,hk)\) for arguments \((x,h)\) and \((y,k)\). The inverse is the lower-block inverse with trailing block \(h^{-1}\). These are the compensating right translations in Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 14.1, p. 106 in the author-posted edition.

The subgroup is closed in the actual real general linear group. Its upper-right block is zero, and its leading block multiplied by the diagonal with first entry equal to the last diagonal entry of the whole matrix is the identity. These two continuous equations force that last entry to be nonzero and determine the leading block. The lower row and last entry give the continuous inverse of the displayed parametrization. The closed-subgroup theorem for linear groups then supplies its exponential Lie algebra. `RealRankRaisingSubgroupStatement` includes the closedness witness, the exponential Lie algebra and the homeomorphism with the row and invertible trailing coordinates.
