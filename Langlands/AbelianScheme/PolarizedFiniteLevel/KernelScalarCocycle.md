# Scalar cocycles on commutative affine group schemes

`UnitTwoCocycle` assigns a unit `c(x,y)` to each pair of points of a group scheme over any test scheme. It requires naturality in the test scheme and the identity

`c(x,y) c(xy,z) = c(y,z) c(x,yz)`.

The module derives the commutator formula from this identity. For a commutative group, `c(x,y) / c(y,x)` is multiplicative in `x` with `y` fixed. If multiplication by `n` is trivial on the group scheme, this ratio has `n`-th power one on every test scheme.

`UnitTwoCocycle.exists_correction_of_exponent` takes a commutative affine group scheme over an algebraically closed field and such an exponent `n`. It produces a global unit `b` on the group satisfying

`b(xy) = b(x) b(y) c(x,y)^n`

on every test scheme. The proof divides the symmetric powered cocycle by its value at the two unit points. This normalized cocycle `d` defines a commutative affine group on the product with the multiplicative group, with law `(x,a)(y,b) = (xy,ab d(x,y))`. Restriction to the scalar subgroup is a surjection of coordinate Hopf algebras. The cocommutative grading has a group-like element of degree one by `CommutativeDecomposition.degree_surjective`. Powers of that element give a Hopf section on the free rank-one character lattice, which gives a retraction to the scalar subgroup. The inverse of the retraction evaluated on `(x,1)` satisfies the correction formula for `d`. Dividing by the value used in normalization gives the formula for `c^n`.

This is the commutative splitting step in the theta-group descent argument of Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary version of 8 February 2012, (8.7)(i) and (8.11). The Library uses split scalar coordinates and the group-like element construction for this step. The source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, printed pp. 115 and 117, PDF pp. 119 and 121.
