# Recovering the `GL_N` Cartan decomposition from the general Cartan theorem

`Langlands.BruhatTits.Cartan.GeneralLinearCartanRecoveryStatement` (universe
`u`) is the implication

```
Geometry.Building.GeneralLinearVertexParahoricStatement.{u} →
  SpecialCompact.GeneralLinearIntegralCartanStatement.{u}
```

This module states the implication and does not prove it.

## The premise

The premise is the vertex comparison of
[`GeneralLinearStatement`](../../Geometry/Building/DepthZero/GeneralLinearStatement.md):
for every nonarchimedean local field \(F\) in universe `u`, every \(N\) and every
`D : KPBuildingDatum` of \(\mathrm{GL}_N\) over \(F\) with
`D.SatisfiesGroupAxioms`, the parahorics of the vertex facets of the reduced
building are exactly the \(G(F)\)-conjugates of
\(K=\mathrm{GL}_N(\mathcal O_F)\), the integral points of
`GeneralLinear.standardIntegralModel`. The chamber comparison is not needed,
and it is not a premise.

The premise identifies subgroups of \(\mathrm{GL}_N(F)\) and says nothing about
double cosets, so on its own it does not imply the conclusion.

## The conclusion

The conclusion is the concrete Cartan bijection
`SpecialCompact.GeneralLinearIntegralCartanStatement`
([statement](../SpecialCompact/GeneralLinearIntegralCartanStatement.md)): for
every such \(F\), every \(N\) and every generic cocharacter \(\nu\) of the
diagonal torus, the positive uniformizer points `C0Plus` of the diagonal torus
for the positive roots of \(\nu\) map bijectively onto
\(K\backslash\mathrm{GL}_N(F)/K\).

## Mathematical route

The implication is the statement that the concrete Cartan decomposition of
\(\mathrm{GL}_N\) is an instance of the general one. It combines the premise
with two theorems of the Library, neither of which is a premise:

- `Langlands.Geometry.Building.groupAxiomsExistence`: every connected
  reductive group over \(F\), in particular \(\mathrm{GL}_N\)
  (`Langlands.GroupScheme.isConnectedReductive_generalLinear`), has a datum `D` with
  `D.SatisfiesGroupAxioms`;
- `Langlands.BruhatTits.Cartan.parahoricCartanConclusions_of_satisfiesGroupAxioms`:
  corrected KP Theorem 5.2.1 for one such datum, giving the bijection between
  the dominant part of \(Z(F)/Z(F)^0\) for a generic cocharacter of the datum's
  maximal split torus and the \(P_x\)-double cosets of \(G(F)\), at every
  special vertex \(x\) of its apartment.

For \(\mathrm{GL}_N\) every vertex is special. Take a datum `D` from the
existence theorem, its maximal split torus \(S\), a special vertex \(x\) of its
apartment, and the vertex facet \(\mathcal F\) of the reduced building that
contains the image of \(x\). The route has three steps.

1. *Two parahorics.* The general theorem is about the apartment parahoric
   \(P_x\) = `D.base.parahoricAt x`. The premise is about the facet parahoric
   `D.parahoric 𝓕`, the neutral integral points of the facet model. The first
   step identifies these two subgroups.
2. *A conjugating element adapted to \(S\).* By the premise
   \(P_x=g_0Kg_0^{-1}\) for some \(g_0\in G(F)\), so \(P_x=\mathrm{GL}(L)\) for the
   lattice \(L=g_0\mathcal O_F^N\). Because \(x\) lies in the apartment of \(S\),
   \(L\) is the direct sum of its intersections with the eigenlines of \(S\). A
   basis of \(L\) adapted to these lines gives \(g\in G(F)\) such that
   \(P_x=gKg^{-1}\) and \(g^{-1}Sg\) is the diagonal torus \(T\).
3. *Transport by inverse conjugation.* The map \(c(z)=g^{-1}zg\) carries
   \(P_x\) to \(K\). It therefore sends the double coset \(P_xzP_x\) to
   \(K\,(g^{-1}zg)\,K\), and this gives a bijection
   \(P_x\backslash G(F)/P_x\to K\backslash G(F)/K\). The same map \(c\)
   carries \(Z(F)=S(F)\) to \(T(F)\) and \(Z(F)^0\) to \(T(\mathcal O_F)\). It
   also carries a generic cocharacter \(\nu\) of \(S\) to the generic
   cocharacter \(g^{-1}\nu g\) of \(T\), and the dominant set for \(\nu\) to the
   dominant set for \(g^{-1}\nu g\).

For the diagonal torus, \(T(F)/T(\mathcal O_F)\) is the cocharacter lattice,
realized by the uniformizer points, and the dominant part is `C0Plus`. Fix a
generic cocharacter \(\nu'\) of \(T\). Apply the general bijection to
\(\nu=g\nu'g^{-1}\) and transport it by \(c\). The result is the concrete
bijection for \(\nu'\).

## Sources

- Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
  Cambridge University Press, 2023: Theorem 5.2.1 and (5.2.1)–(5.2.2)
  (printed pp. 187–188, PDF pp. 218–219) for the Cartan decomposition;
  Proposition 15.1.31 and 15.1.33 (printed pp. 523–524, PDF pp. 554–555) for
  the vertex stabilizers of \(\mathrm{GL}_N\). Literature ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Tasho Kaletha and Gopal Prasad, *Corrections and additions*, version of
  1 November 2024: the corrected inequality (5.2.2) (PDF p. 30). Literature ID
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
