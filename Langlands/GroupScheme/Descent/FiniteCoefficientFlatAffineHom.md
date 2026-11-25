# Finite coefficient models of homomorphisms of affine flat groups

This is an internal construction from finite coefficient models of
affine flat finitely presented groups and the published general homomorphism
descent theorem `Descent.FiniteCoefficient.homGeneral`.

`FlatAffineHomModel R A f` records source and target groups over one finitely
generated `R`-subalgebra of `A`, a homomorphism between them, actual recovery
isomorphisms for both groups, and the commuting recovery square for `f`.
Both model groups are affine, flat and locally of finite presentation. Each
retains the commutativity of its original group when that holds.

`exists_flatAffineHomModel` retains any prescribed finite subset of the base
algebra. First choose a source model, then a target model over an enlargement
of the source's coefficients. Pull the source model to the common coefficients.
General homomorphism descent gives one further finitely generated enlargement
on which the map is defined. Naturality of the direct-versus-iterated pullback
comparison gives the recovery square.

`flatAffineHomModel` chooses such a model.
`FlatAffineHomModel.enlarge` allows any further finite coefficient enlargement,
preserving all structural properties and the recovery square.
`FlatAffineHomModel.noetherian` proves that its coefficient ring is noetherian
whenever the ground ring is.

The construction requires no smoothness or commutativity premise on either
original group. It does not descend any additional property of the
homomorphism, or the exactness of a pair of homomorphisms.
