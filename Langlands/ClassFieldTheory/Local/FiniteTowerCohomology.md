# Cohomology comparisons in a finite Galois tower

Author: Worker 58.

This module constructs the comparisons between the published relative field
cohomology maps and Mathlib's subgroup inflation–restriction maps. It works
over an arbitrary common universe `u` and the unchanged scalar ring
`IntegerScalars.{u}`. A compatible tower `K → L → M` is expressed by the
three algebra instances and `IsScalarTower K L M`. The general kernel
constructions assume `Normal K L`. The invariant-unit and quotient-cohomology
constructions additionally assume `FiniteDimensional K M` and `IsGalois K M`.
They do not require a valuation or a local-field hypothesis.

## Groups and coefficients

`towerRestrictionKernel` is the kernel of `AlgEquiv.restrictNormalHom L`
from `Gal(M/K)` to `Gal(L/K)`. `towerRestrictionKernelEquiv` identifies this
kernel with `Gal(M/L)` by retaining the underlying field automorphism. In
one direction, membership in the kernel proves that the automorphism fixes
the image of `L`; in the other, restriction of scalars gives the kernel
member. The inverse's underlying automorphism is recorded by
`towerRestrictionKernelEquiv_symm_val`.

`towerInvariantUnitInclusion` is the published `unitInclusionLinear L M`
with codomain restricted to `fixedUnitSubmodule K M` for this kernel. Its
invariance certificate follows from fixing the middle field. Its injectivity
follows from injectivity of the field embedding. For surjectivity,
`towerInvariantUnitInclusion_surjective` applies the finite Galois fixed-element
criterion to the value of an invariant unit. That value therefore has a
preimage in `L`; its nonzero property makes the preimage a unit. Finite
dimensionality and the Galois property of `M/L` are obtained from the tower.
`towerInvariantUnitsEquiv` is the resulting linear equivalence from
`Additive Lˣ` to the actual kernel-invariant submodule.

`towerQuotientEquiv` is the first-isomorphism equivalence from
`Gal(M/K) / towerRestrictionKernel K L M` to `Gal(L/K)`, using surjectivity
of normal restriction. `towerQuotientEquiv_mk` states its value on each
representative. This construction itself needs normality of `M/K`, supplied
by the Galois assumption, but does not use finite dimensionality.

## Cohomology and actual maps

`towerKernelCohomologyIso K L M n` identifies the cohomology of the kernel
acting on `Additive Mˣ` with `relativeCohomology L M n`. It uses the group
equivalence above and the identity on coefficients. The identity
`towerKernelCohomologyIso_restriction` proves that subgroup restriction
followed by this isomorphism is exactly `relativeRestriction K L M n`.

`towerInvariantUnitsEquiv_intertwines` proves equivariance of unit inclusion
for the quotient action. Its proof is the normal-restriction commutation
identity on field elements. Quotient induction and the inverse of the
coefficient equivalence then give `towerQuotientCohomologyIso K L M n` from
quotient cohomology with invariant coefficients to `relativeCohomology K L n`.
The identity `towerQuotientCohomologyIso_inflation` says that its inverse
followed by Mathlib's quotient inflation is exactly
`relativeInflation K L M n`. Both map identities use functorial composition
of `groupCohomology.map`, with equality of the group homomorphisms and of
the underlying coefficient linear maps. These identities hold in every
natural degree `n`, including zero.

Finally, `towerKernelH1_subsingleton` transports the published theorem
`finiteRelativeH1Vanishing L M` through the kernel cohomology isomorphism.
It needs only finite dimensionality of `M/K` in addition to the kernel's
normality and tower assumptions. The Galois assumption on `M/K` is omitted
from this theorem. No additional vanishing hypothesis is introduced.

## Provenance and scope

These are derived comparison constructions for Jean-Pierre Serre,
*Local Fields*, English translation (1979), X.4 Proposition 6, printed
page 156 / PDF page 162. That passage identifies the subgroup with
`Gal(M/L)`, the quotient with `Gal(L/K)`, and its invariant coefficients
with `Lˣ`, then applies VII.6 Proposition 5 in degree two. The latter is
on printed pages 117–118 / PDF pages 123–124. The vanishing input is X.1
Proposition 2, printed page 150 / PDF page 156. Worker 58 read these
passages in the registered source `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No project errata entry was present when checked.

The Lean implementation uses explicit group and linear equivalences and
Mathlib's induced cohomology isomorphisms to implement those identifications.
It imports the existing coefficient modules and Hilbert 90 proof without
modification. It does not prove degree-two inflation–restriction exactness:
the generic group-cohomology theorem and its final specialization to the
published finite-tower target remain separate proof obligations. No local
invariant, fundamental class, or absolute cohomology comparison is claimed.
