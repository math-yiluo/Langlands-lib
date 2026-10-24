# Spherical Hecke actions on actual automorphic local components

This module constructs the spherical Hecke action on an actual local invariant
subspace of automorphic forms. It uses the number field and form-carrier universe
`uF`, a finite place `v`, and positive rank `r + 1`. The local subspace
`S : LocalRealization F (r + 1) v` retains its inherited right-translation action
and its inclusion into the actual automorphic form space.

`SphericalVectors` is the fixed submodule for the existing canonical spherical
subgroup. `sphericalHeckeAction` integrates the inherited smooth representation
over the existing spherical corner, with the Haar measure giving this subgroup
mass one. `standardHeckeOperator` evaluates this action on the characteristic
function of the standard diagonal double coset. The zeroth operator is the
identity. These constructions need neither irreducibility nor admissibility.

`sphericalInclusion` is the injective linear map obtained by restricting the
actual inclusion to fixed vectors. It commutes with every spherical-corner
element and hence with each standard operator. If irreducibility and
admissibility are supplied, these local standard operators are definitionally
the operators on `S.padicObject`.

`IsSphericalHeckeEigenvector` requires a nonzero vector and every standard
operator equation. It is equivalent to the ambient automorphic eigenform
relation for the included vector. `HasSphericalHeckeSpectrum` requires a
nonzero fixed submodule and the prescribed scalar equations for **every**
vector in it. With the same explicit irreducibility and admissibility
hypotheses, this is equivalent to the existing spectrum relation on
`S.padicClass`. The whole-space relation can also be checked after inclusion
into ambient forms. A supplied spectrum gives an actual nonzero ambient
eigenform in the component.

The scalars are exactly `Unramified.standardHeckeScalar`, including its positive
square-root residue-cardinality normalization and signed Euler coefficients.
No spectrum is selected or proved to exist from sphericality. No implication
from a single eigenvector to a whole-space spectrum, dimension-one assertion,
Satake classification, or tensor-factorization existence is asserted.

## Provenance and implemented proofs

This is internal derived infrastructure. It combines the actual subspaces and
inclusions from `LocalRealization`, the topology transport and positive-rank
objects from `PadicLocalCategory`, the mass-one double-coset operators and
quotient spectral relation from `Unramified.HeckeOperators`, and the ambient
operators from `SphericalHecke`. The fixed-space inclusion uses
`fixedVectorsMap`; its injectivity uses `fixedVectorsMap_injective`. Entire-corner
compatibility is the specialization of `Hecke.cornerAction_intertwiner` to the
actual inclusion. The eigenvector and whole-space comparisons follow by
linearity and injectivity. The class comparison uses the published
`hasSphericalHeckeSpectrumClass_classOf` theorem, with the unchanged underlying
representation. Finally, `Submodule.ne_bot_iff` provides a nonzero fixed vector,
and the supplied whole-space equations make its inclusion an eigenform.
