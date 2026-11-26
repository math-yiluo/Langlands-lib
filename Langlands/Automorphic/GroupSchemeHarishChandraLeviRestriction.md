# Finite Levi restrictions on the adelic parabolic quotient

`translatedLeviRestriction` sends an ambient function to the function on actual
Levi points given by \(m\mapsto f(l(m)t)\), where \(l(m)\) denotes the image
of \(m\) in the ambient group. It is complex-linear because it is precomposition
with the map \(m\mapsto l(m)t\).

`finiteDimensional_span_of_leviRestrictions` applies to a family of functions
that are left invariant by the adelic unipotent image, fixed by a common open
finite level, and have all their infinite compact restrictions in one
finite-dimensional subspace. Given a finite-dimensional bound on the Levi
restrictions for each finite translate and infinite compact translate, it
proves that the span of the ambient family is finite-dimensional.

The compact finite projection has a finite cover by cosets of the open level.
On the infinite compact, choose a minimal intersection of finitely many
evaluation kernels in the given finite-dimensional subspace. Adding one more
evaluation kernel leaves that intersection unchanged, so the selected
evaluations detect zero. The joint restriction map on the span of the ambient
family thus takes values in a finite product of finite-dimensional Levi
spaces. To prove injectivity, write an ambient point as \(v m k\) using Iwasawa
coverage and the subgroup multiplication isomorphism. Left invariance removes
\(v\). Maximal compactness puts the infinite projection of \(k\) in the
infinite compact, while finite-level invariance replaces its finite projection
by one of the chosen coset representatives. The selected infinite evaluations
then determine the value at the remaining compact point.

The construction is derived from the restriction to Levi translates in
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.17, printed pp. 37–38, PDF pp. 20–21. The registered chapter is
`moeglin-waldspurger-1995-growth-and-constant-terms`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
This finite sampling argument uses the unnormalized restriction and requires
the finite-dimensional Levi bounds as hypotheses.
