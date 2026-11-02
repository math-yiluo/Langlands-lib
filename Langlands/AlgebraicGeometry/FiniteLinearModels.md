# Local finite linear models on scheme slices

This is an internal interface separating the construction of a finite linear
model from the subsequent representation and gluing arguments. Its provenance
is the finite-equation solution presheaf and its scheme representation in
`FiniteLinearEquationsScheme`, together with ordinary restriction to an open
chart of the base.

For a commutative ring object `R`, `FiniteLinearEquations.HasModel F` says that
there are natural numbers `m,n`, an `m` by `n` matrix over `R`, and a natural
isomorphism from `F` to its finite homogeneous solution presheaf. Both
presheaves are on the entire category of schemes over `Spec R`, with values in
`Type (u+1)`. The solution presheaf uses the explicit value lift and global
sections of every test scheme. The premise is therefore stronger than a
comparison on affine tests or geometric points.

`HasLocalModels F` says that the base has an open cover by actual spectra, on
each of which `F` has such a model. The index type and every coefficient ring
are in universe `u`; the open chart maps are jointly surjective on underlying
points. Restriction is precisely precomposition with
`(Over.map (j i)).op`. It retains every test scheme and restriction morphism
over each chart. The base and its cover need not be quasi-compact.

`HasModel.of_iso` and `HasLocalModels.of_iso` transport models through natural
isomorphisms. On each chart, `HasModel.exists_representation` composes the
existing natural isomorphism for the equation spectrum with the inverse of
the model isomorphism. The spectrum's structure map is affine and locally of
finite presentation by the existing instances. Applying this construction
chart by chart proves `HasLocalModels.exists_local_representations`.
`hasModel_solutionsPresheaf` provides the model given by the same matrix.

These definitions and consequences do not assert that any coherent-family
Hom presheaf has local finite linear models. They do not supply a global
representer or a sheaf property. In particular, the chart premises alone give
no descent assertion about values on test schemes whose structure map does not
factor through a chart; a global gluing argument must establish or assume the
appropriate sheaf condition separately.
