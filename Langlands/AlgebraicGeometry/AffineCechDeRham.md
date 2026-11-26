# Degree-one relative Čech–de Rham cohomology

`Langlands.AlgebraicGeometry.AffineCechDeRham.H1` is the degree-one module of
the Čech–de Rham total complex for a smooth separated morphism
\(f\colon X\to\operatorname{Spec} R\) and a supplied finite affine open cover
of \(X\). The commutative base ring, scheme and cover index share an arbitrary
universe. The cover is a `Scheme.AffineOpenCover` with a finite index type.
`coverOpens` takes its open images, and `isAffineOpen_inter` uses separatedness
over the affine base to show that every nonempty tuple of cover members has
an affine intersection.

## Coefficients and restrictions

For an open \(V\), `sectionAlgebras` uses the section ring \(A=\Gamma(X,V)\)
with the \(R\)-algebra structure induced by \(f\). For \(W\subseteq V\) its
map is the restriction of the structure sheaf, as an \(R\)-algebra map.
`functions`, `oneForms` and `twoForms` take \(A\), \(\Omega^1_{A/R}\) and
\(\bigwedge^2_A\Omega^1_{A/R}\) as \(R\)-modules. The map on one-forms
sends \(a\,db\) to \(\rho(a)\,d\rho(b)\) for the ring restriction \(\rho\).
The map on two-forms sends a wedge to the wedge of the corresponding
restricted one-forms by the exterior power's universal property.

`RelativeForms.dZero` is the universal relative derivation.
`RelativeForms.dOne` descends the \(R\)-linear map from the free presentation
of \(\Omega^1_{A/R}\) sending the coefficient \(a\) on the generator \(db\)
to \(da\wedge db\). The map kills every \(A\)-multiple of the additive and
base-ring relations by additivity and vanishing on base scalars. For an
\(A\)-multiple of a Leibniz relation, expansion leaves a multiple of
\(dx\wedge dy+dy\wedge dx=0\). `dOne_smul_d` proves the resulting formula
\(d(a\,db)=da\wedge db\) and `dOne_dZero` uses \(d1=0\).
The restrictions commute with both derivatives. For `dOne_natural`, this
follows from the displayed formula and the additive generation of one-forms
by \(a\,db\). The differentials `exteriorD0` and `exteriorD1` therefore act
on presheaves of \(R\)-modules.

## Total complex and filtration

`Cochains` uses all tuples of cover indices, including repetitions, with the
intersections of `CechResolution.AllSeq`. `cechD` uses the Library's
alternating sum of face restrictions, viewed as an \(R\)-linear map. The
first three total degrees are

\[
C^0=C^{0,0},\qquad C^1=C^{1,0}\oplus C^{0,1},\qquad
C^2=C^{2,0}\oplus C^{1,1}\oplus C^{0,2},
\]

where \(C^{p,q}\) consists of Čech \(p\)-cochains of relative \(q\)-forms.
`D0` and `D1` are the maps

\[
h\mapsto(\partial h,dh),\qquad
(a,b)\mapsto(\partial a,\partial b-da,db).
\]

`D1_comp_D0` uses \(\partial^2=0\), the naturality identity
\(\partial d=d\partial\), and the local identity \(d(dh)=0\).
`boundaryMap` takes values in `cocycles` by this equation. `H1` is the
quotient of `cocycles` by `boundaries`, the range of `boundaryMap` inside
the cocycle module.

`closedForms` consists of one-form families \(b\in C^{0,1}\) with
\(\partial b=0\) and \(db=0\). These are the degree-one cocycles of the
subcomplex of form degrees at least one. `closedFormClass` sends \(b\) to
the class of \((0,b)\) in `H1`, and `hodgeF1` is its image submodule.

## Source correspondence

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, §2.1.6, introduces the relative Kähler de Rham complex
and Čech double complex on printed pp. 129–130 (PDF pp. 157–158). The rule
\(\partial\oplus(-1)^p d\) there gives `D0`. The explicit display on printed
p. 132 (PDF p. 160) gives the three components of `D1`. The paragraph before
(2.1.6.5) on printed p. 135 (PDF p. 163) describes the truncation in form
degrees at least one and the inclusion through \(C^{0,1}\). In degree one
the cocycle condition on that summand gives exactly the compatible closed
forms used in `hodgeF1`. The retained PDF is registered as
`lan-2008-pel-thesis-revision-2021` with SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
[Revised dissertation](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf)
