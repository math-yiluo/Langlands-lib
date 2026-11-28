# Standard Bernstein families through a specified rational parabolic

`BernsteinParabolicPresentationStatement` asserts that for any specified
rational parabolic, rational Levi and geometric unipotent radical of a
connected reductive group over a nonarchimedean local field, there is a
standard Bernstein family and a finite simple-root label whose three standard
subgroup functors are the ranges of the specified maps. The equalities hold
on every test scheme. The family uses the canonical topology on rational
points. The theorem is `bernsteinParabolicPresentation` in namespace
`Langlands.CuspidalSupport`.

This comparison implements the choice of standard position used in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, V.3.9 and V.3.14, printed pp. 112–113 / PDF pp. 118–119.
The choice makes the standard-family descriptions available for the
induction in VI.10.5, printed p. 213 / PDF p. 219, where the parabolic is
arbitrary. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Construction and induction comparison

Apply `exists_isSplitComponent` to the given Levi. The theorem
`parabolicRootPresentationExistence` gives a maximal split torus, a generic
cocharacter, and a simple-root subset presenting the parabolic and Levi.
Construct the standard family using `Jacquet.standardBernsteinFamily` and
filter its finite set of simple roots by membership in the subset. The
resulting `rootSet` equals the original subset by extensionality.

A standard cocharacter realizing the parabolic comes with the root
presentation. `radical_range_eq_dynamic_unipotent` identifies the given
radical range with the dynamic unipotent for that cocharacter, and
`standardCocharacter` identifies it with the standard unipotent subgroup
functor at the same root label.

`BernsteinParabolicPresentation.leviPoints` composes the canonical
`leviPointsEquiv` of the specified Levi with the equality of its point image
and the literal standard Levi. Its composite with the inclusion into the
ambient point group is the point map of the given composite inclusion.
Under the Hausdorff, local compactness, nonarchimedean group and Levi product
hypotheses for normalized induction, `inductionObjIso` specializes all three
range equalities to rational points. It applies `leviInductionObjIsoOfPointImages`
to compare represented induction of a smooth object with standard induction
of the object transported along the inverse Levi point equivalence.
