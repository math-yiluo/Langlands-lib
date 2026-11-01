# Finite separation of inner determinant-slice integrals

This derived helper implements JPSS (1983), Section 6.3, printed pages
433–435, formulas (6)–(9).

For every canonical p-adic field, square Schwartz–Bruhat test `Phi`, and
continuous complex quasicharacter `chi`, a compact open subgroup fixes
`Phi` on the left and is trivial under both `chi(det)` and the normalized
determinant norm. Intersecting it with its inverse-transpose preimage
makes it stable under inverse transpose as well. Since a subgroup is
closed under inversion, this also gives stability under transpose.

For each integer `j` and complex number `s`, the weight is
`1_(ord(det h)=j) Phi(h) chi(det h) |det h|^s`, on the actual general
linear group. The determinant-shell helper proves that its matrix-test
factor has compact support on this group. The other factors are
continuous. Thus its product with every continuous complex function is
integrable for the actual `generalLinearHaar`, with no growth premise.
The weight is left invariant under the chosen subgroup.

For an admissible representation `sigma` in independent universe `uV`,
and its specified standard-character functional `ell`, the published
compact middle-average theorem chooses finitely many model vectors
`B_i`, before any model vector `W`. It then chooses actual bi-smooth
matrix coefficients `f_i` of that same coefficient model, before `j`,
`s`, and the external group element `g`. The theorem proves

`integral weight(h) W(g h) dh =
 sum_i B_i(g) integral weight(h) f_i(h) dh`.

It also proves integrability of the original integrand and of every
summand. The finite-dimensional argument uses only admissibility;
zero models, reducible representations and inner rank one (`r=0`)
are included.

The proof applies the published left-averaging Fubini lemma to the
already integrable slice integrand, cancels the nonzero compact subgroup
Haar mass, substitutes the exact finite middle-average expansion, and
integrates the finite sum. A generic span-induction lemma supplies local
constancy for the entire bi-smooth coefficient span.

The source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 486 visually read printed pages 432–436 and reread printed 433
while implementing this helper. The source indicator
`ord(det(g*h))=m` becomes the present inner slice at
`j=m-ord(det g)`. The uniformity in `j` gives that specialization.
The compactness argument, generic coefficient-span lemma, and explicit
normalization are derived formal packaging. No source-specific
registered errata was found in the bounded project checks recorded by
the adjacent-rank development.

The result concerns only the inner slice calculation. Joint
integrability of the outer quotient variable with the inner group
variable, the initial outer shear and Fubini step, subsequent Laurent
series calculations, functional equations and both parent factor
conclusions remain separate obligations.

Local instances in this module have explicit module-specific names so that its
canonical field structures can be imported together with the model-star modules.
The instance bodies and all mathematical definitions and theorem statements are
unchanged by this compatibility correction.
