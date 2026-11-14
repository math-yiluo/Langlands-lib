# Actual root specialization data from a surviving residue root

Author: Worker 407.

This internal construction produces the published structure
`IntegralRootSpecializationData` (see [RootSpecialization](RootSpecialization.md))
from three ingredients:

- a supplied relative-component model `D` over a local domain `R` with
  specified fraction field `K`;
- a supplied integral torus `T : IntegralTorusData D S i` whose integral
  torus is split (`hT`);
- a supplied special-fibre quotient `Q` satisfying `Q.IsReductiveQuotient`.

The only further input is a generic character `a` whose specialization
`T.characterSpecialization hT a` is a relative root of the image torus
`T.specialFibreInclusion ≫ Q.projection` in the actual reductive quotient.
All declarations are at arbitrary universe `u`. No apartment, building point,
valuation or model-existence statement is assumed or claimed.

## The construction `IntegralTorusData.rootSpecializationData`

Write `ā = T.characterSpecialization hT a`, `t = T.specialFibreInclusion`, and
`π = Q.projection`. Relative roots are nonzero by definition, so `ā ≠ 0`.
Since specialization is an additive equivalence, `a ≠ 0` as well
(`ne_zero_of_characterSpecialization_mem_relativeRoots`). The fields are
filled as follows.

- Generic root and model. `T.toIntegralSplitTorusData hT` (published, in
  `IntegralTorusRootData`) reuses the same integral torus, inclusion and
  generic identification. Its published `rootGroup`, `rootInclusion`,
  `rootModel` and `rootModelMap` (from `IntegralRootFiltration`, built on
  `IntegralModel.SplitRoot`) give the generic root representative, its proof
  `rootInclusion_isRootSubgroup` that it represents
  `RelativeRoot.subgroup i a` on every test, the smooth integral root model
  (`IntegralModel.SplitRoot.model_isSmooth`), and the compatible map
  `toNeutral` into `D.neutral`.

- Residue root group. `exists_residueRootRepresentative` applies the
  published `RelativeRoot.subgroup_isSmoothClosed` to the split special-fibre
  torus, the map `t ≫ π` into the smooth affine quotient, and `ā`. It gives a
  smooth closed representative of the intrinsic root functor. The definitions
  `residueRootGroup` and `residueRootInclusion` choose such a representative.
  It is affine because it is closed in the affine quotient. This is an actual
  root subgroup of the specified reductive quotient `Q.quotient`, not of a
  unipotent group.

- Residue projection. The published `rootModelMap_specialFibre_isRepresentedBy`
  shows that the special-fibre map of the root model represents the root
  functor of `t` and `ā` in the neutral special fibre. Then
  `residueRootProjection` is the published canonical root map
  `RelativeRoot.SmoothQuotient.rootMap t π ā` between the two root
  representatives. `residueRootProjection_comp` is the required commuting
  square
  `residueProjection ≫ residueInclusion = toNeutral.specialFibreMap ≫ Q.projection`.

- Kernel. The kernel field is the full scheme-theoretic kernel of the residue
  projection, with its actual inclusion `kernelι`. The published
  `SpecialFibreQuotientData.projection_smooth` shows that `π` is smooth. The
  fppf-quotient clause of `IsReductiveQuotient` shows that it is surjective.
  The results of [RootSmoothQuotientKernel](../../GroupScheme/Rational/RootSmoothQuotientKernel.md)
  then give the remaining fields:
  - smoothness of the kernel (`rootMap_kernel_smooth`);
  - closedness of its inclusion (`kernelι_rootMap_isClosedSubgroup`);
  - the represented fppf-quotient property of the residue projection
    (`rootMap_isFppfQuotient`);
  - split unipotence (`rootMap_kernel_isSplitUnipotent`).

  The last result is applied to the specified radical inclusion
  `Q.radicalInclusion`. By `IsUnipotentRadical`, the radical is closed,
  smooth and connected, and its range is normal. By the fppf-quotient clause,
  its range is the full kernel of `π`.

The stronger separate predicate
`IntegralRootSpecializationData.RepresentsIntegralRoot` is not asserted.

## Reduction compatibility

`IntegralRootSpecializationData.reductionCompatible_of_neutral` applies to
every `A : IntegralRootSpecializationData T hT Q a` over a Henselian local
domain and every root function family `φ`. It needs `Q.IsReductiveQuotient`
and two hypotheses about generic root points `g ∈ rootGroupPoints i a` that
lie in `D.neutral.integralPoints`:

1. `0 ≤ φ a g`;
2. if `0 < φ a g`, then `g ∈ Q.positivePoints`.

Under these hypotheses it proves
`RootModelReductionCompatible a A.genericInclusion A.model φ A.residueProjection`.

For a root-model section `x`, `genericPoint_mem` shows that its generic point
`g` lies in `rootGroupPoints i a`, using `representsGenericRoot`. By the
naturality of `toNeutral`, `g` is the generic point of a neutral section, so
the first hypothesis gives the first clause. For the second clause, the
second hypothesis supplies a neutral section `y` with generic point `g` whose
reduction lies in the radical points. Since `integralPointMap` is injective
for affine models over a domain, `y` is the image of `x`. The published
`ker_projectionPoints` sends radical points to `1` under `π`. The published
`reduction_comm` then gives
`residueInclusion (residueProjection (reduction x)) = 1`. The inclusion is a
monomorphism, so `residueProjection (reduction x) = 1`.

## Provenance and scope

This is an internal construction from the named published Library results.
It mirrors the role of root models and their split-unipotent kernels in the
proof of Kaletha–Prasad, Proposition 9.4.25. That proposition is not
formalized here. The module does not prove that any particular character
specializes to a root of the quotient. It also does not prove the two value
hypotheses for any actual model. Both remain inputs, to be supplied by
geometric model constructions.
