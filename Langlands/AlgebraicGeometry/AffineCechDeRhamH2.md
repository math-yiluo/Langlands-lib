# Degree-two relative Čech–de Rham cohomology

`Langlands.AlgebraicGeometry.AffineCechDeRham.H2` is the degree-two module of
the Čech–de Rham total complex for a morphism
\(f\colon X\to\operatorname{Spec} R\) and an affine open cover of \(X\), on the
actual rings of sections and their relative Kähler differentials. The module
`Langlands.AlgebraicGeometry.AffineCechDeRhamH2` extends
`Langlands.AlgebraicGeometry.AffineCechDeRham`, which supplies the section
algebras, the one- and two-forms `oneForms` and `twoForms`, the exterior
differentials `exteriorD0` and `exteriorD1`, the Čech cochains `Cochains` with
the alternating differential `cechD`, the total terms `C0`, `C1`, `C2` and the
total differentials `D0` and `D1`. All declarations below live in the namespace
`Langlands.AlgebraicGeometry.AffineCechDeRham`. As for `H1`, the abbreviation
`H2` asks for `f` smooth and separated and for a finite cover index; the
quotient itself does not use these hypotheses.

## Three-forms and their maps

For an \(R\)-algebra \(A\), `RelativeForms.Three R A` is the third exterior
power \(\bigwedge^3_A\Omega^1_{A/R}\), and `RelativeForms.wedgeThree x y z` is
the wedge \(x\wedge y\wedge z\) of three one-forms. The \(A\)-bilinear product
`RelativeForms.wedgeOneTwo` of a one-form and a two-form curries the universal
alternating map in its first argument and lifts the remaining alternating map
of two arguments through the universal property of \(\bigwedge^2_A\). Its value
on a wedge is `wedgeOneTwo_wedge`: \(x\wedge(y\wedge z)=x\wedge y\wedge z\).

For an \(R\)-algebra map \(g\colon A\to B\), `RelativeForms.mapThree g` is the
\(g\)-semilinear map sending \(x\wedge y\wedge z\) to
\(g_*x\wedge g_*y\wedge g_*z\), where \(g_*\) is the existing map
`RelativeForms.mapOne g` on one-forms. It is the universal-property lift of an
alternating map into \(\bigwedge^3_B\Omega^1_{B/R}\), regarded as an
\(A\)-module through \(g\). The identities `mapThree_id` and `mapThree_comp`
are checked on the wedges \(x\wedge y\wedge z\), which span the exterior power.
`mapThree_wedgeOneTwo` shows that the maps respect the product of a one-form
and a two-form.

## The exterior differential on two-forms

The intended formula \(d(x\wedge y)=dx\wedge y-x\wedge dy\) is not
\(A\)-bilinear in \((x,y)\): replacing \(x\) by \(ax\) adds the term
\(da\wedge x\wedge y\). The implementation absorbs this defect into a twisted
module. On the pairs \(J=\bigwedge^2_A\Omega^1_{A/R}\times
\bigwedge^3_A\Omega^1_{A/R}\) the algebra acts by

\[
a\cdot(\omega,\eta)=(a\omega,\ da\wedge\omega+a\eta).
\]

The Leibniz rule \(d(ab)=a\,db+b\,da\) makes this an \(A\)-module. The map
\((x,y)\mapsto(x\wedge y,\ y\wedge dx-x\wedge dy)\), with the existing
`RelativeForms.dOne` as \(d\) on one-forms, is \(A\)-multilinear into \(J\).
The new Leibniz rule `dOne_smul`, \(d(ax)=da\wedge x+a\,dx\), together with
\(y\wedge da\wedge x=da\wedge x\wedge y\), gives linearity in the first
argument. In the second argument the term \(-x\wedge da\wedge y\) equals
\(da\wedge x\wedge y\). The map vanishes when \(x=y\), so it is alternating.
Its lift through the universal property of \(\bigwedge^2_A\) is an
\(A\)-linear map \(\bigwedge^2_A\Omega^1_{A/R}\to J\) whose first component is
the identity, checked on wedges. `RelativeForms.dTwo` is the second component.
It is \(R\)-linear because \(d\) vanishes on the image of \(R\). Since
\(y\wedge dx=dx\wedge y\) for a one-form and a two-form, `dTwo_wedge` reads
\(d(x\wedge y)=dx\wedge y-x\wedge dy\).

The \(A\)-linearity of the lift is the Leibniz rule `dTwo_smul`,
\(d(a\omega)=da\wedge\omega+a\,d\omega\). With \(d(db)=0\) from
`dOne_dZero` it gives `dTwo_smul_wedge_d`:

\[
d(a\,db\wedge dc)=da\wedge db\wedge dc.
\]

`dTwo_dOne` proves \(d(d\omega)=0\) for every one-form. One-forms are sums of
terms \(a\,db\), and \(d(a\,db)=da\wedge db\), so it suffices that
\(d(da\wedge db)=d(da)\wedge db-da\wedge d(db)=0\). `dTwo_comp_dOne` states
the same identity for the composite map. `dTwo_natural` shows
\(d(g_*\omega)=g_*(d\omega)\) by induction over the span of the wedges. On a
wedge it combines `dTwo_wedge` with naturality of `dOne` and
`mapThree_wedgeOneTwo`. For an \(A\)-multiple it uses the Leibniz rule on both
sides and \(g_*(da)=d(g(a))\).

## The presheaf of three-forms

`threeForms` takes an open \(V\) to the three-forms of the section ring
\(\Gamma(X,V)\) as an \(R\)-module, with restrictions given by `mapThree` of
the restriction maps. `exteriorD2` is the map of presheaves
`twoForms f ⟶ threeForms f` given by `dTwo` on each open; its naturality is
`dTwo_natural`.

## The total differential in degree two

Writing \(C^{p,q}\) for Čech \(p\)-cochains of relative \(q\)-forms,
`C3` is \(C^{3,0}\oplus C^{2,1}\oplus C^{1,2}\oplus C^{0,3}\). Lan's rule
\(D=\partial\oplus(-1)^pd\) on \(C^{p,q}\) gives, on
\(C^2=C^{2,0}\oplus C^{1,1}\oplus C^{0,2}\),

\[
D_2(a,b,c)=(\partial a,\ \partial b+da,\ \partial c-db,\ dc),
\]

which is `D2`, with components recorded by `D2_apply`. The signs are those
of `D1`, \((a,b)\mapsto(\partial a,\partial b-da,db)\).

`D2_comp_D1` proves \(D_2\circ D_1=0\). For \((a,b)\in C^1\),

\[
D_2D_1(a,b)=\bigl(\partial^2a,\ \partial^2b-\partial da+d\partial a,\
\partial db-d\partial b+d\,da,\ d\,db\bigr).
\]

The Čech differential squares to zero (`cechD_cechD`), it commutes with the
componentwise exterior differentials (`cechD_cochainMap`), and \(d\,da=0\) and
\(d\,db=0\) hold chartwise by `dOne_dZero` and `dTwo_dOne`. So every component
vanishes.

## Cocycles, boundaries and classes

`cocyclesTwo` is the kernel of `D2`. `boundaryMapTwo` is `D1` with codomain
restricted to `cocyclesTwo`, which is possible by `D2_comp_D1`, and
`boundariesTwo` is its range. `H2` is the quotient of `cocyclesTwo` by
`boundariesTwo`. `mem_cocyclesTwo_iff` describes cocycles by components: an
element \((a,b,c)\) is a cocycle exactly when \(\partial a=0\),
\(\partial b+da=0\), \(\partial c=db\) and \(dc=0\). `mem_boundariesTwo_iff`
identifies the boundaries with the cocycles in the range of `D1`, and
`mk_eq_mk_iff` states that two cocycles have the same class exactly when their
difference lies in that range.

`closedOverlapForms` consists of the overlap one-forms \(\omega\in C^{1,1}\)
with \(\partial\omega=0\) and \(d\omega=0\). Since
\(D_2(0,\omega,0)=(0,\partial\omega,-d\omega,0)\),
`zero_overlap_zero_mem_cocyclesTwo_iff` shows that \((0,\omega,0)\) is a
cocycle exactly when \(\omega\) lies in `closedOverlapForms`.
`closedOverlapCocycle` is the resulting \(R\)-linear map into `cocyclesTwo`,
and `closedOverlapClass` composes it with the quotient map to `H2`.
`mk_eq_closedOverlapClass` identifies the class of any cocycle with components
\((0,\omega,0)\) with `closedOverlapClass` of \(\omega\).
`closedOverlapClass_eq_iff` says that the classes of \(\omega\) and
\(\omega'\) agree exactly when \((0,\omega-\omega',0)\) is in the range of
`D1`. `closedOverlapClass_eq_zero_iff` says that the class of \(\omega\)
vanishes exactly when there are \(a\in C^{1,0}\) and \(b\in C^{0,1}\) with
\(\partial a=0\), \(\partial b-da=\omega\) and \(db=0\).

## Source correspondence

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, §2.1.6, printed pp. 129–130 (PDF pp. 157–158), defines
the relative de Rham complex with differentials induced by the universal
derivation, the Čech differential
\((\partial x)_{\alpha_0\dots\alpha_{p+1}}=\sum_k(-1)^kx_{\alpha_0\dots
\widehat{\alpha_k}\dots\alpha_{p+1}}\), and the total differential
\(D=\partial\oplus(-1)^pd\) on \(C^{p,q}\), noting that \(\partial d=d\partial\)
gives \(D^2=0\). `D2` is this rule in total degree two, and `D2_comp_D1` is the
corresponding instance of \(D^2=0\). The explicit display on printed p. 132
(PDF p. 160) gives the three components of `D1`, with the same signs. The
retained PDF is registered as `lan-2008-pel-thesis-revision-2021` with SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
[Revised dissertation](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf)

The twisted-module construction of `dTwo` is internal to this module. The
source uses the exterior derivative of the relative de Rham complex, and
`dTwo_smul_wedge_d` records its formula
\(d(a\,db\wedge dc)=da\wedge db\wedge dc\) on the terms
\(a\,db\wedge dc\).
