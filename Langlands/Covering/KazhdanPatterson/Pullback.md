# Determinant pullback and twisting

`Langlands.KazhdanPatterson.determinantEmbedding` sends a matrix \(g\) in \(\mathrm{GL}_r(R)\) to \(\operatorname{diag}(g,\det(g)^{-1})\) in \(\mathrm{SL}_{r+1}(R)\) for a commutative ring \(R\). The definition uses a block matrix, with the extra coordinate last. The block determinant is the product of \(\det(g)\) and its inverse. Block multiplication proves multiplicativity, and the upper-left entries recover \(g\).

For a supplied normalized central cocycle \(\sigma\) on \(\mathrm{SL}_{r+1}(R)\) and a multiplicative pairing \(b\) on \(R^\times\), `twistedPullbackCocycle` constructs the normalized cocycle

\[
(g,h)\longmapsto \sigma(\iota(g),\iota(h))\, b(\det(g),\det(h))^e .
\]

`blsPullbackCocycle` uses \(e=-1\), the determinant correction in Banks–Levy–Sepanski. With their symbol taken to be the inverse of the Hilbert symbol \(H\) in Kazhdan–Patterson's convention, that correction is \(H(\det(g),\det(h))\). The additional Kazhdan–Patterson twist is \(H(\det(g),\det(h))^c\). Accordingly `kpPullbackCocycle` takes exponent \(c+1\) on the direct pullback, and `kpPullbackCocycle_apply` proves the pointwise equality with the corrected pullback times the \(c\)-twist. The direct pullback has exponent zero at \(c=-1\). The exponent in Lean is an integer. For coefficients in \(\mu_n\), the power depends only on its residue modulo \(n\).

The formula takes the special-linear cocycle as input. Its arithmetic specialization uses the special-linear cocycle from the Banks–Levy–Sepanski section with the inverse Hilbert symbol as its Steinberg symbol. Comparing that section with the original Kazhdan–Patterson section requires a separate coboundary computation.

## Sources

- Banks, Levy, and Sepanski, *Block-compatible metaplectic cocycles*, §3, printed p. 146, PDF p. 16, embedding and defining equation immediately before Lemma 1. Literature ID `banks-levy-sepanski-1999-block-compatible`, SHA-256 `328a218c96be42f879ab31b299e260cff3932ca5cef330ab0eb7046905a5f35e`. [DOI](https://doi.org/10.1515/crll.1999.507.131)
- Kazhdan and Patterson, *Metaplectic forms*, §0.1, printed pp. 39, 41 and 43, PDF pp. 6, 8 and 10, diagonal cocycle, determinant twist and the restriction from a larger special linear group. Literature ID `kazhdan-patterson-1984-metaplectic-forms`, SHA-256 `0f91142e8fc3814981fb77e3a3f05a7359ebd4a5e9afdf5386eb357cb4f2b57e`. [DOI](https://doi.org/10.1007/BF02698770)
