# Unramified descent of KP building data

`KPBuildingDatum.SatisfiesUnramifiedDescent D` is the unramified descent
predicate on the given datum for a connected reductive group \(G\) over a
nonarchimedean local field \(F\), in either characteristic. It uses Axiom
4.1.27 with UR 3 in the set form explained below. The predicate uses
`inertiaFixedField F` for the maximal unramified extension \(K\) and
`baseChanged F K G` for \(G_K\). The reference upper apartment comes from
a special \(F\)-torus containing the datum's \(S\), as in §§9.2.2–9.2.3.
`UnramifiedBuildingDescent.buildingData` forms the upper datum from that
torus and a Galois-stable equipollence class of valuations satisfying V 6.

`UnramifiedBuildingDescent.semilinearData` gives the coefficient action on
this very apartment, where `KPApartmentData.galoisAffineAction` is its affine
form. On the reduced quotient this action agrees with
`KPApartmentData.galoisQuotientAction` by `semilinearData_action_apply`.
The action transports the apartment \(g A\) to \(\sigma(g) A\) by the
coefficient action on the coordinates in \(A\). This implements the action
of Axiom 4.1.17 used in §9.2.1 and Proposition 7.9.5. The same action gives
the fixed loci in UR 1 and UR 2.

- **UR 1** asserts that \(e\) is injective, equivariant along `rationalExtend`,
  and has range equal to the group fixed locus. The domain and codomain are
  the reduced building quotients of the given data.
- **UR 2** writes an apartment of the lower datum in the chart \(g A(S)\), with
  torus \(gSg^{-1}\). Every maximal \(F\)-split torus is obtained this way
  by rational conjugacy (`smoothMaximalSplitTorusConjugacy`). The equivariant
  torus-to-apartment correspondence is the one in Axiom 4.1.1
  (`ValuationBuildingData.HasTorusApartmentCorrespondence`).
  `IsSpecialTorusInChart` says that \(T\) is an \(F\)-torus embedded as a
  closed subgroup, that the chart torus factors through \(T\), and that \(T_K\)
  is a maximal \(K\)-split torus. A special torus exists in every chart.
  For each such \(T\), the upper chart \(h A(C.S)\) represents \(A(T_K)\)
  by the exhibited conjugating isomorphism \(t\).
  The affine injection \(a\) in `HasUnramifiedApartmentComparison`
  agrees with \(e\) in the two charts and its range consists exactly of the
  fixed points in the upper chart. Its linear part is the pushforward of
  real cocharacters via \(S_K \to T_K \xrightarrow{t^{-1}} C.S\) on reduced
  translation spaces. This is the affine structure of the fixed apartment
  with the \(V(S)\)-action of §9.2.3 and Proposition 9.3.16.
- **UR 3** gives the equality
  `AffineRootSystem.restrictedRoots a C.affineRoots = D.base.affineRoots`
  in the same charts. Every lower affine root has an upper lift, and every
  nonconstant upper restriction is a lower affine root. The linear part of
  \(a\) gives the pullback of the derivative on reduced cocharacters.
  Conjugating the chart tori transports their roots and affine functions
  (`relativeRootsTransportEquiv` and `KPApartmentData.affineRootsTransportEquiv`).
- **UR 4** uses the actual index \(\Omega\) of `D.models` for every nonempty
  bounded subset of an apartment. Its image \(e(\Omega)\) is nonempty and
  bounded in an upper apartment by UR 2. Indeed an affine functional on
  the upper apartment pulls back to an affine functional on the lower one.
  `HasUnramifiedModelComparison` uses the characterization in Theorems
  8.3.2 and 8.3.13 of the two upper models by their integral point subgroups.
  Corollary 2.10.11 gives uniqueness over the strictly Henselian
  valuation ring of \(K\).
  These are the intersections of the pointwise fixer of \(e(\Omega)\) with
  the character-valuation kernel \(G(K)^1\) and with \(G(K)^0\), respectively.
  `UnramifiedZeroDatum.zeroPoints` gives the latter subgroup by Definition
  2.6.23(1). One such datum is used for all subsets.
  Each upper model is isomorphic to the fixed-field integer base change
  (`baseChangeUnramified`) of the corresponding model of `D.models`, with
  identity on the identified generic fibre. Both intersection laws are
  included as equalities of subgroups of \(G(F)\), using `Subgroup.comap`
  along scalar extension to express intersection with \(G(F)\).

## The affine-root lift

The paragraph introducing Proposition 9.4.28 states the set equality used
here. In its proof, take \(z\) where a lower affine root vanishes. By
Proposition 9.4.23 its derivative is a root of the reductive quotient at
\(z\). Over the residue extension this root is the restriction of **some**
root of the base-changed reductive quotient. Applying Proposition 9.4.23
upstairs gives a lift vanishing at \(z\). In the other direction, a
nonconstant restriction vanishes somewhere in the fixed apartment, and
the same proposition and restriction of the quotient roots show that
it is a lower affine root. The Library proves the set form on valuation
apartments in `unramifiedAffineRootRestriction`.

The quantifier in the printed UR 3 and Proposition 9.4.28 asks for a lift
for every upper generic-fibre root restricting to the given derivative.
That fails for inner type \(A\). Let \(F=\mathbb Q_3\), let \(L/F\) be its
unramified quadratic extension, and take \(G=\mathrm{GL}_2(D_0)\) for the
quaternion division algebra \(D_0=(L/F,\pi)\) with \(\pi=3\). The scalar pairs
on the two \(D_0\)-lines give a maximal split torus \(S\). Indeed, a split
torus acts through at most two weights on the two-dimensional right
\(D_0\)-space. The \(L^\times\) factors on the two lines give a special torus.
Over \(K\) the group splits as \(\mathrm{GL}_4\) and \(S_K\) acts with
diagonal entries \((s,s,t,t)\).

In the splitting \(\ell\mapsto\operatorname{diag}(\ell,\bar\ell)\) and
\(j\mapsto J=\begin{pmatrix}0&\pi\\1&0\end{pmatrix}\), Frobenius acts by
coefficient Frobenius followed by conjugation by \(\operatorname{diag}(J,J)\).
It takes \(u_{34}(1)\) to \(u_{43}(\pi^{-1})\). In the split valuation
apartment the value on \(u_{ij}(c)\) is \(\operatorname{ord}_K(c)+x_i-x_j\).
Equality of the two values on the fixed chart thus gives \(x_3-x_4=-1/2\).
Both upper derivatives \(x_1-x_3\) and \(x_1-x_4\) restrict to the same
nonzero lower derivative. The restriction of \(x_1-x_3\) gives a lower
affine root by the converse in UR 3. Every upper affine root of the second
derivative has the form \(x_1-x_4+n\) for \(n\in\mathbb Z\). Its restriction
differs from that of \(x_1-x_3\) by \(n-1/2\). The set equality retains the
lift the reductive-quotient argument gives. The split valuation and
integer jumps used here are those of §6.1(a), Proposition 6.2.6 and
Definition 6.3.4. The inner-type-\(A\) building is described in §10.7(a).

## Sources

The source is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Axiom 4.1.27, pp. 165–166 (PDF pp. 196–197), with Axiom 4.1.17, p. 162
(PDF p. 193), and Proposition 7.9.5, p. 276 (PDF p. 307). Sections 9.2.1–9.2.5,
Propositions 9.3.4, 9.3.16, 9.3.24, 9.4.23 and 9.4.28, and §9.5 explain the
four clauses on the descended data. The authors' *Corrections and additions*
(1 November 2024), PDF p. 39, give the revised finite-orbit and fixed-point
arguments in §9.2.1. PDF p. 37 corrects the proof of Theorem 8.3.13 and sets
the perfect-residue scope of §8.3, which holds here because the residue
field is finite. PDF p. 27 supplies the corrected Definition 4.1.26 used by
the assignment predicate in `FullValidity.Assignment`.
