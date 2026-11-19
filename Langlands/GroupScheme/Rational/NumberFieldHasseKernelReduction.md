# Arithmetic kernels for the number-field Hasse principle

`Cocycle.LocallyTrivial` means triviality after base change to the actual
pullback cover at every place of a number field. The propositions
`NumberFieldSimplyConnectedGaloisHasseKernelStatement` and
`NumberFieldAdjointGaloisHasseKernelStatement` each assert that, for the
indicated class of groups and a finite Galois cover, a locally trivial
cocycle is trivial on the original cover. They quantify over all number
fields and finite Galois covers in universe `u`.

`numberFieldGaloisHassePrinciple_of_arithmetic` starts from a pair of cocycles
with a cohomology relation over every completion. In the simply connected
and adjoint cases, it descends the inner form associated with the first
cocycle, using affineness and flat surjectivity of the cover. The inner
form belongs to the same class by invariance under field extension and
isomorphism. The difference cocycle is locally trivial in the inner form.
Applying the corresponding arithmetic kernel hypothesis gives a global
trivialization, which the difference criterion converts to the required
cohomology relation on the original group.

For the orthogonal case the theorem applies the reduction to native
quadratic isometry. Finally, `numberFieldHassePrinciple_of_arithmetic`
uses the finite-Galois reduction to obtain the unchanged target for all
finite separable covers. Its premises are the two kernel propositions and
the native number-field quadratic-isometry proposition.

This is an internal reduction on the exact natural cocycles and their
completion pullbacks. The three global arithmetic premises remain proof
obligations for the unconditional Hasse principle.
