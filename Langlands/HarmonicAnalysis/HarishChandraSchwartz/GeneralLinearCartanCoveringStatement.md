# Cartan coverings for the general linear group and its standard Levis

`GeneralLinearCartanCoveringStatement` specializes the covering clauses of
Renard V.5.1(4) and (5) to the actual group scheme \(\mathrm{GL}_N\) over an
arbitrary nonarchimedean local field \(F\). The common subgroup \(K\) is the
image of the integral points of the standard group scheme
\(\mathrm{GL}_{N,\mathcal O_F}\). The torus is the diagonal torus, and
the reference cocharacter has strictly decreasing integer coordinates, which
select the upper triangular positive system and its adjacent simple roots.
The statement includes the cases of zero and one coordinate.

The two conclusions are `FiniteCartanCovering` for \(\mathrm{GL}_N(F)\)
and `StandardLeviCartanCovering` for every standard Levi \(M_J(F)\).
The first uses \(K\) and the simple roots of the ambient group. The second
uses \(K\cap M_J(F)\) and the simple roots \(J\) of the Levi. Each
conclusion provides a finite set of centralizer points \(f\) and a
decomposition \(k_1 f a k_2\) for each point, with \(k_1,k_2\) in the
respective compact subgroup and \(a\) a torus uniformizer power on which
each specified simple root has absolute value at most one.

The specialization comes from the integral–diagonal–integral matrix
Cartan decomposition applied to \(\mathrm{GL}_N(F)\) and to the blocks
of each standard Levi. The diagonal power itself supplies \(a\), so the
matrix decomposition gives the witness \(\{1\}\) for the finite set.
The proposition records the two covering interfaces used by the
Schwartz-weight and constant-term estimates.

## Sources

- Renard, *Représentations des groupes réductifs p-adiques*, French edition of
  9 July 2026, V.3.23, printed p. 117 (PDF p. 123), and V.5.1(4)–(5),
  printed p. 122 (PDF p. 128). Literature ID
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
  Harish-Chandra)*, I.1(4), printed p. 241 (PDF p. 7), and the use of
  the Levi Cartan decomposition in the proof of II.4.5, printed p. 262
  (PDF p. 28). Literature ID `waldspurger-2003-plancherel`, SHA-256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
