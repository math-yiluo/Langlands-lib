# Unramified scalar extension of the Lie quotient with two models

The module `Langlands.GroupScheme.IntegralModel.CongruenceLieTruncationUnramified`
extends the Lie quotient of `CongruenceLieTruncation` to the maximal unramified
extension.

Let \(F\) be a nonarchimedean local field, of either characteristic, with
valuation ring \(\mathcal O_F\). Let \(K\) be the fixed field of inertia in a
separable closure (`inertiaFixedField F`) and \(\mathcal O_K\) its valuation
ring (`fixedFieldIntegers F`). Let \(G\) be an affine group scheme over \(F\)
and \(M,N\) integral models of \(G\) over \(\mathcal O_F\); `baseChangeUnramified`
gives their base changes to \(\mathcal O_K\), integral models of \(G_K\). The
generic tangent extension `GenericLie.baseChange` from the Lie algebra of \(G\)
to that of \(G_K\) is semilinear over \(\mathcal O_F\to\mathcal O_K\).

- `baseChangeUnramified_mem_lieLatticeAt` shows that `GenericLie.baseChange`
  sends the level-\(n\) scaled Lie lattice \(\mathfrak m_F^n\operatorname{Lie}(M)\)
  into \(\mathfrak m_K^n\operatorname{Lie}(M_{\mathcal O_K})\). The proof
  combines `baseChange_mem_lieLattice` (the unscaled lattice is preserved),
  the locality of \(\mathcal O_F\to\mathcal O_K\) and `Ideal.map_pow`, which
  give \(\mathfrak m_F^n\mathcal O_K\subseteq\mathfrak m_K^n\).
- `N.unramifiedTruncatedCongruenceLieQuotientMap M n` is the semilinear map
  \[
  L_{N,n}/(L_{N,n}\cap L_{M,n})\longrightarrow
  L_{N_{\mathcal O_K},n}/(L_{N_{\mathcal O_K},n}\cap L_{M_{\mathcal O_K},n})
  \]
  induced (`Submodule.mapQ`) by `GenericLie.baseChange`, using the
  preservation of the level-\(n\) lattices of both \(N\) and \(M\).
- `unramifiedTruncatedCongruenceLieQuotientMap_mk` records that it sends the
  class of a tangent vector \(X\in L_{N,n}\) to the class of its scalar
  extension.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023),
Theorem 13.5.1(1), which asks for the isomorphism
\(G(k)_{x,r}/G(k)_{x,s}\to\mathfrak g(k)_{x,r}/\mathfrak g(k)_{x,s}\) to be
compatible with unramified extensions, and the first paragraph of its proof
under condition (2), printed pp. 474–475 (PDF pp. 505–506). This map is the
Lie-side map for that compatibility. The module contains no statement
comparing it with `truncatedCongruenceLieHom` on congruence subgroups.
