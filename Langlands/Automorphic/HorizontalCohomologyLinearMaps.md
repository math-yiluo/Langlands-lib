# Underlying linear maps of actual horizontal transport

Author: Worker 2.

For a number field `F : Type u` in an arbitrary universe, positive natural
rank `n` (`NeZero n`), actual complex operator realizations `S` and `T`,
a full operator intertwiner `A : S.Intertwiner T`, and every natural degree
`q`, this internal API identifies the linear maps underlying the existing
finite adelic cycle and cohomology intertwiners.

`horizontalCyclesMap_toLinearMap` identifies
`(Intertwiner.horizontalCyclesMap A q).toLinearMap` with
`Horizontal.mapCycles` applied to the degreewise linear maps underlying
`A.horizontalMap`. These are the existing actual horizontal cochain maps
given by coefficient postcomposition. The cycle carrier is the kernel
of the actual restricted differential.

`horizontalCohomologyMap_toLinearMap` identifies
`(Intertwiner.horizontalCohomologyMap A q).toLinearMap` with
`Horizontal.mapCohomology` for the same degreewise linear maps.
That constructor descends the cycle map using `Submodule.mapQ` and its
proved preservation of actual image boundaries. The quotient and its
degree-zero convention are unchanged.

The private `horizontalLinearMap_chain` supplies the chain equation
expected by these generic linear constructors. It takes the symmetry of
the already proved actual `horizontalMap_differential` and unfolds
`Horizontal.differential`, `horizontalDifferential`, and
`horizontalEquivariantSubmodule` to identify the wrappers. Both public
formulas are typed proof abbreviations with reflexive proofs: the
published actual intertwiners already use those linear constructors.
The new private proof of their compatibility equation is identified with
the existing proof by proof irrelevance; no new compatibility premise is
required.

Ten named local additive groups are canonical `Submodule.addCommGroup`
structures: five function-space stages, two realization spaces, two exact
generic horizontal cochain spaces, and the generic cycle-space family.
They alter neither carriers nor operations.

The provenance is internal specialization of the published
`HorizontalCohomologyTransport`,
`Langlands.Cohomology.Lie.HorizontalCohomologyIntertwiner`, and
`Langlands.Cohomology.Lie.HorizontalCohomologyTransport` definitions and
their underlying-map formulas. The full standard infinite compact group
and every-slot horizontal conditions are retained. This pair adds the two
linear-map identifications; analytic and sheaf comparisons, quotient
topology or smoothness, finiteness, nonvanishing, and spectral existence
remain separate obligations.
