# Original analytic and algebraic coefficient cohomology with Hecke actions

This internal construction fixes an actual number field `F`, a nonzero
natural rank `n`, the finite embedding index `I` with map `e`, and the
original matrix group-scheme representation `ρ` on the finite coordinate
index `m`. It uses the existing full analytic and algebraic coefficient
carriers and their actual diagonal tensor Lie and compact actions on an
`OperatorRealization F n`. Both complex-place orientations, empty finite
indices and every natural cochain degree remain included. The number field
has its existing independent universe; the coefficient indices have the
same universe scope as the original coefficient construction.

The four cycle and cohomology smoothness results specialize
`HorizontalCohomologyHecke` to the original analytic or algebraic compact
representation, its actual reduced tensor Lie action, the proved
infinitesimal insertion law, original finite translation and its proved
chain compatibility. Smoothness of the original tensor horizontal cochains
is already proved in `HorizontalFiniteHecke`, with no finite-dimensional
coefficient premise. These specializations use the original differential
kernels and quotients by differential-image boundaries, including zero
boundaries in degree zero. No comparison space replaces either quotient.

For a Borel measurable structure and Haar measure `μ` on the actual finite
adelic general-linear group, the six named Hecke actions integrate its
original finite actions on the analytic and algebraic cochains, cycles and
cohomology. Each is a nonunital complex algebra homomorphism from the
existing measure-indexed Hecke algebra to the endomorphisms of the original
space. The existing convolution and Haar normalization are inherited.

The six differential, cycle-inclusion and class-projection compatibility
laws are direct specializations of the generic integration laws. The three
analytic-to-algebraic comparison laws apply
`Hecke.integratedAction_intertwiner` to the original coefficient comparison
in each degree, its original cycle equivalence and its original quotient
equivalence. The quotient comparison uses the generic
`HorizontalCohomologyHeckeEquivalence` helper before specializing to the
original tensor chain equivalence. Thus the two independently constructed quotient actions agree
through the actual comparison, with no additional compatibility premise.

The provenance is internal composition of published original-action
coefficient cohomology and its finite intertwiners with the smoothness and
measure-indexed integration constructions. It adds no external-source
identification, admissibility, cohomological finite-dimensionality,
nonvanishing, coefficient occurrence, automorphic existence or geometric
comparison theorem.
