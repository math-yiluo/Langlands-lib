# Proof of the solvable radical of the general linear group

The theorem `generalLinearSolvableRadical` proves
`GeneralLinearSolvableRadicalStatement`. For every field \(k\), the scalar
embedding \(\mathbf G_m\to\mathrm{GL}_{n+1}\) and, in size zero, the identity
section of the trivial torus are geometric solvable radicals
(`IsGeometricSolvableRadical`): each is the solvable radical over \(k\) and
its base change is the solvable radical over the algebraic closure of \(k\).
This specializes the solvable radical and connected centre assertions of
David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, V.2.1, printed p. 104 (PDF p. 110), to
\(\mathrm{GL}_n\). The proof below uses that the centre of \(\mathrm{GL}_n\)
is a torus. It does not follow Renard's text.

## A torus centre is the solvable radical

Let \(G\) be a connected reductive group over a field, and let \(z\colon Z\to
G\) be a scheme-theoretic centre (`IsSchemeTheoreticCenter`) with \(Z\) a
torus. Then \(z\) satisfies every field of `IsSolvableRadical`:

- \(z\) is a closed subgroup, by the first part of
  `IsSchemeTheoreticCenter`;
- \(Z\) is smooth and connected because it is a torus;
- \(Z\) is commutative, since a central closed subgroup is commutative
  (`IsCentral.commGroupScheme`), so it is solvable
  (`isSolvableGroupScheme_of_isCommMonObj`);
- the image of a central morphism is normal (`IsCentral.range_isNormal`).

For greatestness, let \(H\to G\) be a smooth connected solvable normal closed
subgroup. \(G\) is affine over the base, so \(H\) is too. The theorem
`IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive_field`
shows that \(H\to G\) is central. So on every test scheme its image lies in
the centre, which is the image of \(z\) by the second part of
`IsSchemeTheoreticCenter`.

The same argument works after base change to the algebraic closure.
Connected reductivity persists by
`IsConnectedReductive.baseChange_toAlgebraicClosure`, tori persist by
`IsTorus.baseChange`, and the base change of a scheme-theoretic centre is
again a scheme-theoretic centre by
`schemeTheoreticCenterBaseChangeStatement`. So a torus centre of a connected
reductive group is a geometric solvable radical.

## The two cases

`GeneralLinear.isConnectedReductiveStatement` shows that
\(\mathrm{GL}_m\) is connected reductive in every size \(m\), including
\(m=0\).

For size \(n+1\), the scalar torus is the split torus \(\mathbf G_m\)
(`isSplitTorus_gm`). Its embedding is a closed subgroup
(`GeneralLinear.isClosedSubgroup_scalarTorus`) whose image on every test
scheme is the centre (`GeneralLinear.range_scalarTorus_eq_center`).

For size zero, the trivial torus is a torus (`isTorus_trivialTorus`) and its
identity section is a closed subgroup (`isClosedSubgroup_trivialTorusHom`).
Through `GeneralLinear.pointsEquiv`, every point of \(\mathrm{GL}_0\) over a
test scheme is an invertible \(0\times 0\) matrix, so it is the identity.
Hence both the image of the identity section and the centre are the trivial
subgroup on every test scheme. So the identity section represents the
centre.
