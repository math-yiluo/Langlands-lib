# The cocycle extension of the diagonal torus

For a multiplicative pairing \(H : U\times U\to A\) of abelian groups, `torusCocycle`
uses the pairing `torusPairing H c` as a normalized two-cocycle with trivial
coefficient action. `TorusCover` is its cocycle extension on \(A\times U^r\).
For \(U=F^\times\), \(A=\mu_n(F)\) and \(H\) the Hilbert symbol, the formula at
\(c=0\) is the diagonal construction of Kazhdan and Patterson. The determinant
factor for an arbitrary integer \(c\) is their twist from the same section.

`torusCommutatorPairing` divides the pairing by its transpose. The group law
gives \(xy=\iota(B(t,s))\,yx\) for lifts \(x,y\) of \(t,s\). Multiplying by
\((yx)^{-1}\) gives `torusCover_commutator` in the convention
\(xyx^{-1}y^{-1}\). Since the coefficient inclusion is injective and each
diagonal tuple has a lift, `torusCover_mem_center_iff` identifies the center as
the inverse image of the left radical of \(B\).

With \(H(b,a)=H(a,b)^{-1}\), `torusCommutatorPairing_eq` evaluates the pairing as
\[
B(t,s) = H\!\left(\prod_i t_i,\prod_i s_i\right)^{2c+1}
         \left(\prod_i H(t_i,s_i)\right)^{-1}.
\]
The proof exchanges the indices in the transposed product, joins the upper and
lower triangular products, and extracts the diagonal factors from the full
product. Bilinearity evaluates that full product on the two determinants. The
two determinant twists contribute a power of \(2c\). This recovers the displayed
commutator on p. 39 at \(c=0\).

## Source

Kazhdan and Patterson, *Metaplectic forms*, §0.1, printed pp. 39 and 41,
PDF pp. 6 and 8, give the diagonal cocycle, the commutator at \(c=0\), and
the determinant twist. Literature ID `kazhdan-patterson-1984-metaplectic-forms`,
SHA-256 `0f91142e8fc3814981fb77e3a3f05a7359ebd4a5e9afdf5386eb357cb4f2b57e`.
[DOI](https://doi.org/10.1007/BF02698770)
