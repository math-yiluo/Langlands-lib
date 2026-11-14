# Common maximal residue tori from bounded generic torus points

This internal result constructs the common residue-torus witness needed for a
comparison of two supplied smooth integral models. It is derived from published
Library results; it is not a new translation of an assertion in the literature.

## Statement

`IntegralModel.BoundedTorusCommonSpecialFibreStatement.{u}` quantifies over:

- a Henselian noetherian valuation domain `R` with algebraically closed residue
  field `k`, and its fraction field `K`;
- a connected reductive `K`-group `G`, two smooth integral models `M` and `N`
  of `G`, and an actual model morphism `ψ : M.Hom N (𝟙 G)`;
- a valuation `v` of `K` with values in any linearly ordered commutative group
  with zero in `Type u`, such that `v` is one on the units of `R`;
- a prescribed maximal split torus `iT : T → G` whose character-valuation
  kernel maps into `M.integralPoints`.

It produces an actual commutative group scheme `S` over `k` and a homomorphism
`s : S → M.specialFibre` such that both `s` and `s ≫ ψ.specialFibreMap` are
maximal tori. Both use the same source `S`. Maximality means a closed torus
subgroup maximal among all closed torus subgroups, using the published
`IsMaximalTorus` predicate.

The residue field need not be finite; its algebraic closedness is an assumption.
There is no characteristic restriction. Smoothness of both models is retained.
No connectedness of either special fibre is assumed. The morphism need not be
surjective or closed, and no kernel or quotient hypothesis is imposed. The unit
bound is required only in `M`.

## Integral construction and proof

`Hom.exists_common_splitTorus_of_bounded` gives more than the bundled
statement. It constructs a split commutative group scheme `𝒮` over `R`, an
isomorphism from its generic fibre to the original `T`, and closed subgroup
maps `jM : 𝒮 → M.group` and `jN : 𝒮 → N.group`. The generic map of `jM` is the
prescribed `iT` precomposed with that isomorphism. The construction satisfies
the literal equality `jM ≫ ψ.hom = jN`, and the residue maps of both `jM`
and `jN` are maximal tori.

First, `Hom.map_mem_integralPoints` carries the bound from `M` to `N`,
because the generic map of `ψ` is the identity. Choose a splitting of `T`
with finite index set `I`. Apply
`SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded`
to each model using this same splitting. The two maps have the same source
`SplitTorusClosure.torus R I`, the same generic-fibre identification, and
the same generic map in `G`.

The source torus is flat and split. The published
`Hom.comp_eq_of_genericTorusMap_eq` therefore gives the integral equality
`jM ≫ ψ.hom = jN`. The generic map of each inclusion is maximal split by
the published `IsMaximalSplitTorus.iso_comp`. Apply the published
`isMaximalTorus_specialFibre_of_generic` separately to the two smooth
models to obtain maximality of both residue inclusions.

`Hom.exists_common_maximalTorus_specialFibre_of_bounded` takes the residue
fibre of `𝒮` and the residue map of `jM`. Base change of the integral equality
identifies its composite with `ψ.specialFibreMap` with the residue map of `jN`.
This proves the two maximalities for exactly the same residue source.
`boundedTorusCommonSpecialFibre` packages this conclusion into the named
Prop-valued statement.

## Published inputs and scope

The direct imports are
`Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus` and
`Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit`. The first supplies
the fixed-splitting closed-torus construction, generic rigidity and residue
maximality; the second supplies the source-isomorphism transport of maximal
splitness. The basic integral-point naturality is in
`Langlands.GroupScheme.IntegralModel`.

This unit constructs the common torus from actual model and bounded-point
data. It does not construct the models, their morphism or the source unit
bound. It neither lifts an arbitrary prescribed residue torus to `R` nor
establishes the facet-to-parabolic correspondence, a special apartment or
the prescribed-building-point conclusion. In particular,
`UnramifiedFixedPointSplitTorusStatement` remains open.
