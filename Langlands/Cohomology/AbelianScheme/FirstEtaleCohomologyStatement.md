# Degree-one étale cohomology and the dual of the Tate module

J. S. Milne, *Abelian Varieties*, author revision of 2 January 2022,
§15, Theorem 15.1(a), p. 27 (PDF p. 27), identifies the integral
degree-one étale cohomology of an abelian variety over an algebraically
closed field with the linear dual of its Tate module. The proof on
pp. 27–28 constructs the natural map from the fundamental group and the
multiplication covers and proves it is an isomorphism. Registered source
ID `milne-abelian-varieties-1986-author-2022`, SHA-256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.

`Langlands.Cohomology.AbelianFirstEtale.AbelianFirstEtaleCohomologyStatement`
asserts a family of \(\mathbb Z_p\)-linear isomorphisms

\[
 H^1_{\mathrm{et}}(A,\mathbb Z_p)\cong
 \operatorname{Hom}_{\mathbb Z_p}(T_p A,\mathbb Z_p)
\]

for abelian schemes over the spectrum of an algebraically closed field
\(K\) in universe zero, with \(p\) a prime and \(p\ne0\) in \(K\).
For each homomorphism \(f:A\to B\) the isomorphisms intertwine pullback
on cohomology with precomposition by \(T_p f\).

`firstAdicCohomology` uses the inverse limit of the first ordinary
étale cohomology of the constant reductions \(\mathbb Z_p/p^r\) on the
actual scheme. `firstAdicCohomologyPullback` applies the geometric pullback
and the canonical constant-coefficient comparison at every reduction.
Their naturality in the coefficient module supplies the map between
the limits. The Tate limit is
`Langlands.AbelianScheme.Tate.PrimeAdic.Integral` evaluated on the
identity test scheme over \(K\). Its transitions come from the
multiplication maps on the actual torsion points, and its maps in \(A\)
are `Langlands.AbelianScheme.Tate.PrimeAdic.map`.

The proposition uses the naturality of Milne's comparison through those
multiplication covers. It asserts naturality in homomorphisms of
abelian schemes over the fixed field. The description of the map through
torsors, comparison over a varying base, and compatibility in coefficient
powers remain distinct from this geometric-fibre statement.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, p. 98 (PDF p. 106), uses the dual of the
standard Tate representation to express the coefficient sheaf through
\(R^1\pi_*\) of the tautological abelian scheme. This proposition is
the geometric-fibre input for that comparison. The relative identification
also requires proper base change and compatibility with the torsion
sheaves of the family. Registered ID
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
