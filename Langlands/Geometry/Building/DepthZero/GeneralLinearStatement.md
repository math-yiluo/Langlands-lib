# `GL_N` comparisons for the parahorics of KP building data

This module states five propositions comparing the facet objects of valid
Kaletha–Prasad building data for \(G=\mathrm{GL}_N\) with the Library's concrete
subgroups of \(\mathrm{GL}_N(F)\). It states them and does not prove them.

## Common setting

Each proposition quantifies over a nonarchimedean local field \(F\) of either
characteristic (`IsNonarchimedeanLocalField F`, universe-polymorphic), every
\(N\in\mathbb N\), and every
`D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))`
with `D.SatisfiesGroupAxioms` (the one-group clauses of the corrected KP
Definition 4.1.26). No other premise is used, except the bounds on \(N\) noted
in the last two propositions, each attached only to the conclusion that needs it.

- \(K=\mathrm{GL}_N(\mathcal O_F)\) is
  `(GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints`, the
  integral points of the standard model
  ([integral model](../../../GroupScheme/IntegralModel/GeneralLinearLattice.md)).
- \(I\) is `generalLinearIwahoriPoints F N`, the preimage in \(K\) of the upper
  triangular group of \(\mathrm{GL}_N(k_F)\)
  ([standard Iwahori subgroup](../../../BruhatTits/IntegralModels/GeneralLinearIwahoriComparison.md)).
- \(q\) is `Nat.card 𝓀[F]`, the order of the residue field.
- Facets are the facets of the reduced building (`BuildingFacet`). A *vertex
  facet* is a facet `x` with `x.val = {y}` for a vertex `y` of the reduced
  building (`D.base.IsVertex y`); a *chamber* is a facet `C` with
  `D.base.IsChamber C.val`.
- \(P_x\), \(P_{x,0+}\), \(\bar G_x(k_F)\) are `D.parahoric x`,
  `D.parahoricRadical x` and `D.finiteReductiveQuotientGroup x hD` of
  [`Definitions`](Definitions.md): the integral points of the neutral facet
  model, the preimage in \(P_x\) of the residue-field points of the supplied
  radical, and the residue-field points of the supplied reductive quotient.
  The neutral special fibre is `(D.models.facetModels.model x).neutral.specialFibre`.
- The conjugate \(gQg^{-1}\) of a subgroup \(Q\) is written
  `Q.map (MulAut.conj g).toMonoidHom`, the convention of `KPParahoric`.

The comparisons are up to \(G(F)\)-conjugacy. A valid datum's maximal split
torus need not be the diagonal torus, and its apartment need not contain the
lattice class of \(\mathcal O_F^N\), so an equality \(P_x=K\) for a fixed facet
would be false for some data.

## The propositions

**`GeneralLinearVertexParahoricStatement`.** For every vertex facet `x` there
is \(g\in G(F)\) with \(P_x=gKg^{-1}\); conversely, for every \(g\in G(F)\) there
is a vertex facet `x` with \(P_x=gKg^{-1}\). So the vertex parahorics are exactly
the conjugates of \(\mathrm{GL}_N(\mathcal O_F)\).

**`GeneralLinearChamberParahoricStatement`.** For every chamber `C` there is
\(g\) with \(P_C=gIg^{-1}\); conversely, every \(gIg^{-1}\) is \(P_C\) for a chamber
`C`. So the chamber parahorics, which are the Iwahori subgroups of KP
Definition 7.4.5(2), (4), are exactly the conjugates of the standard Iwahori
subgroup.

**`GeneralLinearVertexDepthZeroStatement`** (hyperspecial case). For every
vertex facet `x`:

1. the neutral special fibre is connected reductive (`IsConnectedReductive`);
2. `Nat.card` of \(\bar G_x(k_F)\) is \(\prod_{i<N}(q^N-q^i)=|\mathrm{GL}_N(k_F)|\);
3. for every \(g\) with \(P_x=gKg^{-1}\), the subgroup \(P_{x,0+}\) is normal in
   \(P_x\) and there is a multiplicative equivalence
   \(e:P_x/P_{x,0+}\simeq\mathrm{GL}_N(k_F)\) such that, whenever \(p\in P_x\) and
   \(u\in\mathrm{GL}_N(\mathcal O_F)\) satisfy \(g^{-1}pg=u\) as matrices (through
   `GeneralLinear.rationalPointsEquiv` and `glIntegralInclusion`), \(e\) sends the
   class of \(p\) to the reduction `glResidueMap F N u`.

**`GeneralLinearChamberDepthZeroStatement`** (Iwahori case). For every
chamber `C`:

1. `Nat.card` of \(\bar G_C(k_F)\) is \((q-1)^N\);
2. for every \(g\) with \(P_C=gIg^{-1}\), the subgroup \(P_{C,0+}\) is normal in
   \(P_C\) and there is a multiplicative equivalence
   \(e:P_C/P_{C,0+}\simeq(k_F^\times)^N\) (the group `Fin N → 𝓀[F]ˣ`) whose
   \(i\)-th coordinate on the class of \(p\) is the residue of the \(i\)-th
   diagonal entry of \(u\), whenever \(g^{-1}pg=u\in\mathrm{GL}_N(\mathcal O_F)\);
3. if \(N\ge 2\), the neutral special fibre is not connected reductive. It is
   connected (a fibre of a relative identity component), so it is not reductive.

The premise \(N\ge2\) is needed only in item 3: for \(N\le1\) the reduced
building is a point, which is both a vertex and a chamber, and the neutral
special fibre there is reductive.

The isomorphisms in item 3 of the vertex statement and item 2 of the chamber
statement are asserted for *every* conjugating element \(g\), and \(e\) may
depend on \(g\). This is consistent: two choices differ by an element of the
normalizer of \(K\) (respectively \(I\)), and \(P_{x,0+}\) is the largest normal
pro-\(p\) subgroup of \(P_x\), which is \(g(1+\varpi M_N(\mathcal O_F))g^{-1}\) for
every such \(g\) (respectively \(gI^+g^{-1}\), where \(I^+\) is
`generalLinearIwahoriPositivePoints F N`, the preimage in \(K\) of the upper
unipotent group of \(\mathrm{GL}_N(k_F)\)). For the Iwahori subgroup a
different choice of \(g\) can permute the diagonal coordinates cyclically,
which is why \(e\) depends on \(g\).

**`GeneralLinearVertexStabilizerStatement`.** For every vertex `y` of the
reduced building and the facet `x` containing it, \(P_x\) equals
`D.base.compactStabilizer y`, that is \(G(F)^1\cap G(F)_y\); and if \(N\ge1\),
\(P_x\) is a proper subgroup of the full stabilizer `D.base.fixer y`. The
premise \(N\ge1\) is needed only for strictness: the scalars \(F^\times\) act
trivially on the reduced building and a uniformizer scalar has determinant
\(\varpi^N\notin\mathcal O_F^\times\), while for \(N=0\) the group is trivial and the
two stabilizers coincide.

## Why these hold

For \(\mathrm{GL}_N\) one has \(G(F)^0=G(F)^1=\{g:\det g\in\mathcal O_F^\times\}\),
the reduced building is the building of lattice classes, and the stabilizer in
\(G(F)^0\) of a periodic lattice chain is the group stabilizing each of its
lattices (KP 15.1.33). Every vertex corresponds to a single lattice class, with
stabilizer \(\mathrm{GL}(L)=g\,\mathrm{GL}_N(\mathcal O_F)\,g^{-1}\) in \(G(F)^1\)
(KP Proposition 15.1.31); every chamber to a complete periodic chain, whose
image in \(\mathrm{GL}(L_0/\varpi L_0)\) is a Borel subgroup with reductive
quotient \((\mathbb G_m)^N\) (KP 15.1.33). All vertices of the type
\(\tilde A_{N-1}\) affine root system are hyperspecial, so the neutral model at
a vertex is reductive and at a chamber with \(N\ge2\) it is not (KP Proposition
8.4.14, whose proof compares \(\dim G=\dim S+\#\Phi\) with the dimension
\(\dim S+\#\Phi_F\) of the reductive quotient). The quotient \(P_x/P_{x,0+}\) is
identified with \(\bar G_x(k_F)\) by reduction (KP §13.2.6). The compact
stabilizer \(G(F)^1_y\) is a maximal bounded subgroup (KP Theorem 4.2.15), and
for \(\mathrm{GL}_N\) it equals \(P_y\) because \(G(F)^0=G(F)^1\) (KP 15.1.33).

## Sources

- Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
  Cambridge University Press, 2023 (PDF page = printed page + 31):
  Proposition 15.1.31, Remark 15.1.32 and 15.1.33 (printed pp. 523–524, PDF
  pp. 554–555); Definition 7.4.5 (printed p. 256, PDF p. 287); Theorem 4.2.15
  (printed p. 173, PDF p. 204); Proposition 8.4.14 (printed p. 306, PDF
  p. 337); §13.2.6 (printed p. 470, PDF p. 501). Literature ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Tasho Kaletha and Gopal Prasad, *Corrections and additions*, version of
  1 November 2024: the corrected axiom list of Definition 4.1.26 (PDF p. 27),
  whose one-group clauses form `SatisfiesGroupAxioms`. The corrections change
  none of the other places cited above. Literature ID `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
