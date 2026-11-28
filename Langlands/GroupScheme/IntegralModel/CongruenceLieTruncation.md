# The congruence–Lie map with a second model in the denominator

The module `Langlands.GroupScheme.IntegralModel.CongruenceLieTruncation` projects
the congruence–Lie homomorphism of one integral model to a Lie quotient whose
denominator comes from a second integral model of the same generic group.

Let \(R\) be a local domain with fraction field \(K\), let \(G\) be an affine
group scheme over \(K\), and let \(M,N\) be integral models of \(G\) over
\(R\) (affine, flat and of finite type, with their identifications of the
generic fibre with \(G\)). For a positive integer \(j\) write
\(L_{N,j}=\mathfrak m^j\operatorname{Lie}(N)\) for the scaled Lie lattice
`N.lieLatticeAt j` inside the generic Lie algebra, and \(L_{M,j}\) likewise.

- `N.truncatedCongruenceLieQuotient M n` is the \(R\)-module
  \(L_{N,n}/(L_{N,n}\cap L_{M,n})\): the quotient of `N.lieLatticeAt n` by the
  preimage of `M.lieLatticeAt n` under the inclusion into the generic Lie
  algebra.
- `truncatedCongruenceLieHom hN hnm hm hL` is defined when \(N\) is smooth
  (`hN : N.IsSmooth`), \(n\le m\le 2n\) are positive integers and
  \(L_{N,m}\subseteq L_{M,n}\) (`hL`). It is the homomorphism from the
  level-\(n\) congruence subgroup `N.congruenceSubgroupAt n` to the additive
  group of `N.truncatedCongruenceLieQuotient M n` (written multiplicatively)
  obtained by composing the canonical `N.congruenceLieHom hN hnm hm`, with
  values in \(L_{N,n}/L_{N,m}\), with the linear projection
  \[
  L_{N,n}/L_{N,m}\longrightarrow L_{N,n}/(L_{N,n}\cap L_{M,n})
  \]
  induced by `hL` (`Submodule.factor`).
- `truncatedCongruenceLieHom_apply` records that the value at \(g\) is the
  image under this projection of the value of `N.congruenceLieHom` at \(g\).

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023),
Theorem 13.5.1 and the first paragraph of its proof, printed pp. 474–475
(PDF pp. 505–506). Under condition (2), \(r=r_0+n\) and \(s\le r_0+2n\), the
proof applies Proposition A.5.19 (printed pp. 641–643) to the model
\(\mathcal G_{x,r_0}\) to compare \(G(k)_{x,r_0+n}/G(k)_{x,r_0+2n}\) with
\(\mathfrak g(k)_{r_0+n}/\mathfrak g(k)_{r_0+2n}\), and then passes to the
quotient by \(\mathfrak g(k)_{s}\), using the model at \(s_0=s-n\). In the
present notation \(N\) is the model at \(r_0\), \(M\) is the model at
\(s-n\) and \(m=2n\); the inclusion \(L_{N,2n}\subseteq L_{M,n}\) corresponds
to \(\mathfrak g(k)_{r_0+2n}\subseteq\mathfrak g(k)_{s}\).

The module constructs the projected map only. It uses the canonical
congruence–Lie homomorphism of Proposition A.5.19(3) and the lattice
inclusion `hL`; it does not state or use the bijectivity in
Proposition A.5.19, and it contains no statement about the kernel or the
image of `truncatedCongruenceLieHom`.
