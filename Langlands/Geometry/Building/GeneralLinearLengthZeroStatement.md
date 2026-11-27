# The length-zero part of the Iwahori–Weyl group of \(\mathrm{GL}_N\)

This module states one regression example for Kaletha–Prasad building data of
\(G=\mathrm{GL}_N\), \(N\ge1\): the length-zero part
\(\Omega_C=\widetilde W^0_C\) of the Iwahori–Weyl group is infinite cyclic,
isomorphic to \(G(F)/G(F)^0\cong\mathbb Z\) through \(\operatorname{ord}\circ\det\),
and for \(N\ge2\) its generators rotate the \(N\) vertices of the chamber. It
states this and does not prove it.

## Setting

`GeneralLinearLengthZeroStatement` quantifies over a nonarchimedean local field
\(F\) of either characteristic (`IsNonarchimedeanLocalField F`,
universe-polymorphic), every \(N\in\mathbb N\), and every
`D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))`,
with the premises `D.SatisfiesGroupAxioms` and \(1\le N\). Write `P = D.base`.

- \(N(F)\) is `normalizerPoints P.i`, \(Z(F)^0\subseteq N(F)\) is
  `P.normalizerZero`, and the Iwahori–Weyl group
  \(\widetilde W^0=N(F)/Z(F)^0\) is `P.IwahoriWeylGroup`
  ([`IwahoriWeyl`](IwahoriWeyl.md)).
- \(G(F)^0\) is `P.zeroSubgroup` (KP Definition 2.6.23), and
  `P.toComponents : W̃^0 → G(F)/G(F)^0` is induced by \(N(F)\subseteq G(F)\).
- For a chamber `C` of the apartment (`AffineRootSystem.IsChamber P.affineRoots C`),
  `P.chamberStabilizer C` is the image in \(\widetilde W^0\) of the stabilizer
  `P.normalizerStabilizer C` of `C` in \(N(F)\): the group
  \(\widetilde W^0_C\) of KP 7.8.2. The affine Weyl group is the separate
  subgroup `P.affinePart`, the kernel of `toComponents`; this statement does
  not identify the two.
- The vertices of `C` are the points `x` of the apartment such that `{x}` is a
  face of `C` (`AffineRootSystem.IsFaceOf P.affineRoots {x} C`).
- \(\rho:G(F)\to\mathrm{GL}_N(F)\) is the matrix of a point
  (`GeneralLinear.rationalPointsEquiv`), and \(\operatorname{ord}:F^\times\to\mathbb Z\)
  is `Plancherel.fieldOrderUnits F` (the normalized valuation, with
  \(\operatorname{ord}(\varpi)=1\)), valued in `Multiplicative ℤ`.

## The statement

`Z(F)^0` is normal in \(N(F)\) and \(G(F)^0\) is normal in \(G(F)\) (these are
existential instance arguments, as in the Library's
`ParahoricBuildingData.IwahoriWeylChamberSplitting`), and:

1. there is an isomorphism \(e:G(F)/G(F)^0\simeq\mathbb Z\) with
   \(e(gG(F)^0)=\operatorname{ord}(\det\rho(g))\);
2. for every chamber `C` of the apartment:
   1. `P.chamberStabilizer C` is isomorphic to \(\mathbb Z\);
   2. `toComponents` restricted to `P.chamberStabilizer C` is a bijection onto
      \(G(F)/G(F)^0\);
   3. if \(N\ge2\): for every \(n\in N(F)\) stabilizing `C` whose class
      generates `P.chamberStabilizer C` (`Subgroup.zpowers`), there is a vertex
      \(x_0\) of `C` such that \(x_0,nx_0,\dots,n^{N-1}x_0\) are distinct, they
      are exactly the vertices of `C`, and \(n^Nx_0=x_0\). So `C` has \(N\)
      vertices and \(n\) permutes them as one cycle of length \(N\);
   4. the pointwise fixer `P.pointwiseFixer` of the image of `C` in the reduced
      building equals `Subgroup.center ⊔ P.parahoric C`, the product
      \(F^\times\cdot P_C\) of the scalars (the centre of \(\mathrm{GL}_N(F)\)) and
      the Iwahori subgroup \(P_C=Z(F)^0\cdot G(F)^\sharp_C\) of KP
      Definition 7.4.1(4);
   5. if \(N\ge2\): this pointwise fixer is a proper subgroup of the setwise
      stabilizer of the image of `C` (`MulAction.stabilizer` for the pointwise
      action of \(G(F)\) on subsets of the reduced building).

## Premises

`D.SatisfiesGroupAxioms` is the standing premise. Its apartment axioms
(`affineRootSystem.apartmentAxioms`, which is
`D.base.SatisfiesApartmentAxioms`) are the hypothesis of the Library's
`iwahoriWeylChamberSplitting` (KP 7.8.2), which gives the normality instances,
`W̃^0 = W_aff ⋊ W̃^0_C` and clause 2.2 for every connected reductive group; the
statement restates clause 2.2 for \(\mathrm{GL}_N\) beside the new clauses.

\(1\le N\) is needed for clauses 1 and 2.1: for \(N=0\) the group is trivial and
\(G(F)/G(F)^0\) is not \(\mathbb Z\). \(2\le N\) is attached only to clauses 2.3
and 2.5: for \(N=1\) the reduced building is a single point, which is both the
chamber and its only vertex, and every element of \(G(F)=F^\times\) fixes it, so
the setwise stabilizer equals the pointwise fixer.

## Why it holds

For \(\mathrm{GL}_N\), \(G(F)^0=G(F)^1=\{g:\det g\in\mathcal O_F^\times\}\) (KP
15.1.33; Definition 2.6.23, with \(G(F)^\natural=\mathrm{SL}_N(F)\) and
\(Z(F)^0\) the integral points of the split torus \(Z=Z_G(S)\)), so
\(\operatorname{ord}\circ\det\) induces \(G(F)/G(F)^0\cong\mathbb Z\), surjective
because of \(\operatorname{diag}(\varpi,1,\dots,1)\). By KP Theorem 7.8.1(1) and
7.8.2, \(\widetilde W^0_C\cong G(F)/G(F)^0\), which gives clauses 2.1 and 2.2.

In a basis adapted to the apartment, the chamber `C` corresponds to the lattice
chain \(\varpi L_0\subsetneq L_{N-1}\subsetneq\dots\subsetneq L_0\) of KP 15.1.24,
and its \(N\) vertices are the classes \([L_i]\), where \(L_i\) has entries in
\(\mathfrak m\) in the first \(i\) coordinates and in \(\mathcal O_F\) in the others.
Let \(\tau\in N(F)\) be the matrix with \(\tau e_j=e_{j+1}\) for \(j<N\) and
\(\tau e_N=\varpi e_1\). Then \(\det\tau=\pm\varpi\), so
\(\operatorname{ord}\det\tau=1\) and the class of \(\tau\) generates
\(\widetilde W^0_C\); \(\tau L_i=L_{i+1}\) for \(i<N-1\) and
\(\tau L_{N-1}=\varpi L_0\), so \(\tau\) rotates the vertices of `C` as one
\(N\)-cycle; and \(\tau^N=\varpi\cdot1\) acts trivially on the reduced building. Another representative \(n\) of a generator differs from
\(\tau^{\pm1}\) by an element of \(Z(F)^0\), which acts trivially on the
apartment; this gives clause 2.3.

An element fixing every vertex \([L_i]\) of `C` maps each \(L_i\) to
\(\varpi^{k_i}L_i\), and the inclusions
\(\varpi L_0\subsetneq L_i\subseteq L_0\) force all \(k_i\) to be equal; so it is
a scalar times an element stabilizing every \(L_i\), and the latter group is the
Iwahori subgroup \(G(F)^0_C=P_C\) (KP 15.1.33). This gives clause 2.4. The
element \(\tau\) stabilizes the image of `C` without fixing it pointwise, which
gives clause 2.5; KP Proposition 7.7.12 identifies \(\widetilde W^0_C\) with
\(\mathcal N/I\) for the normalizer \(\mathcal N\) of the Iwahori subgroup
\(I=P_C\).

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach` (PDF page = printed page + 31):

- Definition 2.6.23 (\(G(k)^0\)), printed p. 104, and Example 2.6.31, printed
  p. 107, where \(G(k)^0\) is a proper subgroup of \(G(k)^1\) for
  \(\mathrm{PGL}_2\); for \(\mathrm{GL}_N\) the two agree (15.1.33);
- Proposition 7.7.12, printed p. 272; Theorem 7.8.1 and 7.8.2
  (\(\widetilde W^0=W_{\mathrm{aff}}\rtimes\widetilde W^0_C\),
  \(\widetilde W^0_C\cong G(k)/G(k)^0\)), printed pp. 272–273;
- 15.1.24 (the standard chamber and its vertices \([L_i]\)), printed p. 521;
  15.1.33 (\(G(k)^0=G(k)^1\) and the stabilizers of lattice chains), printed
  p. 524.

The 2024 corrections (`kaletha-prasad-2024-corrections`, version of 1 November
2024) correct the proof of injectivity in Theorem 7.8.1(2) and add Theorem
7.8.1(4); parts (1) and 7.8.2, used here, are unchanged.
