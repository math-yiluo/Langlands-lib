# Compact open refinement at an actual finite place

For a number field `F`, a finite place `v`, and any natural matrix rank `n`,
`FiniteAdelicGL.compactOpenRefinement F n v U` is the intersection of the
existing local integral subgroup with the given open subgroup `U` of
`FiniteLocalGL F n v`. The group is the actual general linear group over the
adic completion, with its existing topology. The field universe is arbitrary.

The intersection is an open subgroup by the lattice structure on
`OpenSubgroup`. It is contained in `U`. It is compact because the local
integral subgroup is compact and `U` is closed. The latter is Mathlib's
general fact that an open subgroup of a topological group is closed.
`compactOpen_cofinal` packages this explicit refinement as the cofinality
condition used by admissible duality and Hilbert smooth-vector recovery.
There is no positive-rank assumption.

This is internal construction infrastructure. It uses the published
`localIntegral` and `isCompact_localIntegral` from `LocalFactor` and
Mathlib's `IsCompact.inter_right` and `OpenSubgroup.isClosed`. The same
intersection argument already appears inside the published
`Automorphic.LocalHecke.automorphicLocalHeckeAction_exists_localUnit`;
this unit exposes the refinement independently of representations and Haar
measures. It requires no new local-field identification, Haar choice,
total-disconnectedness hypothesis or representation-theoretic premise.
