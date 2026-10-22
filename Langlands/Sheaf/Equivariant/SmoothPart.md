# The smooth part of an equivariant sheaf

Author: Worker 13. Built on Worker 13's published smoothness predicate
`Langlands.Sheaf.Equivariant.Smooth` and the published transport category
`Langlands.Sheaf.Equivariant.ActionOpens` with its subgroup arrows
`invariantArrow`.

Let `R` be a commutative ring and `G` a group with a topology acting on a
topological space `X`. The space `X`, `R` and the module carriers lie in one
universe `u`, and `G` lies in a universe `uG`. A section `s` over `U` is
*smooth* when it is locally fixed in the sense of the published
`IsLocallyFixedAt` at every point of `U`. This module shows that, under the
hypotheses below, the smooth sections of an equivariant module sheaf form the
largest smooth equivariant subsheaf. The resulting smooth part is right
adjoint to the inclusion `smoothInclusion` of smooth sheaves.

## Stable neighbourhoods

`HasStableNeighbourhoods G X` is a class of the following form. For every point
`x` and every open `O` containing `x`, there are an open subgroup `H` and an
open `V` with `x ∈ V ⊆ O` and `h • V ⊆ V` for all `h ∈ H`. Two instances are
proved.

- `hasStableNeighbourhoods_of_discreteTopology`: for a discrete group, take
  the trivial subgroup and `V = O`.
- `hasStableNeighbourhoods_of_nonarchimedeanGroup`: for a
  `NonarchimedeanGroup` acting continuously (`ContinuousSMul`), continuity of
  the action at `(1, x)` gives a neighbourhood `N` of `1` and an open `W₀ ∋ x`
  with `N • W₀ ⊆ O`. An open subgroup `H ⊆ N` exists by the nonarchimedean
  property, and `V = ⋃_{h ∈ H} h • W₀` is open, contains `x`, lies in `O` and
  is stable under `H`.

## Local fixedness

The following lemmas need no hypothesis beyond the actions.

- `map_invariantArrow_map_eq`: let `H` fix a section `t` over an `H`-stable
  open `V`, and let `f : W ⟶ V` be a transport arrow with label `g`. Let `H'`
  stabilize `W` with `g h g⁻¹ ∈ H` for `h ∈ H'`. Then `H'` fixes the image of
  `t` under `f`. Composing `f` with an arrow of `H'` equals composing an arrow
  of `H` with `f`, by a group identity of the labels.
- `map_inclusionHom_map_inclusionHom`: restricting twice is restricting once.
- `IsLocallyFixedAt.of_restrict`: if the restriction of `s` to a smaller open
  is locally fixed at `x`, so is `s`.
- `IsLocallyFixedAt.map`: morphisms of transport presheaves preserve local
  fixedness, by naturality for the inclusion and the subgroup arrows.
- `IsLocallyFixedAt.smul`: scalar multiples of locally fixed sections are
  locally fixed.

With `HasStableNeighbourhoods G X` alone:

- `isLocallyFixedAt_zero`: the zero section is locally fixed at every point of
  its open, on a stable neighbourhood inside it.
- `IsLocallyFixedAt.exists_common`: two sections locally fixed at the same
  point, possibly of different presheaves and over different opens, are fixed
  by one open subgroup on one stable neighbourhood. Take the intersection of
  the two subgroups with a subgroup stabilizing a small neighbourhood inside
  both witnesses, and apply `map_invariantArrow_map_eq` to the inclusions.
- `IsLocallyFixedAt.add`: sums of locally fixed sections are locally fixed.

If in addition `G` is a topological group (`IsTopologicalGroup`) and every
translation is continuous (`ContinuousConstSMul`):

- `IsLocallyFixedAt.map_arrow`: let `f : W ⟶ U` have label `g`. If `s` is
  locally fixed at `g • x` and `x ∈ W`, then its image under `f` is locally
  fixed at `x`. The witness is a stable neighbourhood of `x` inside
  `W ∩ g⁻¹V`, where `V` witnesses fixedness at `g • x`. The fixing subgroup
  is the intersection of its stabilizer with the preimage of the old subgroup
  under conjugation by `g`. That preimage is open because conjugation is
  continuous.
- `IsLocallyFixedAt.restrict`: restriction to a smaller open containing the
  point preserves local fixedness (the case of label one).

## Smooth sections and the smooth subsheaf

The next declarations assume all of the hypotheses above.

`smoothSubmodule R F U` is the submodule of sections over `U` that are locally
fixed at every point of `U`. Closure under zero, sums and scalars is the three
lemmas above, and `mem_smoothSubmodule_iff` unfolds membership.
`map_mem_smoothSubmodule` proves that restriction and group transport preserve
smooth sections, by `IsLocallyFixedAt.map_arrow`.

`smoothPresheaf R F` is the transport presheaf of smooth sections, with the
restricted maps of `F`. `smoothPresheafι` is its inclusion into `F`, and
`smoothPresheafMap` and `smoothPresheafFunctor` make it functorial in `F`.

`smoothPresheaf_isSheaf` proves that if `F` satisfies the published sheaf
condition, so does `smoothPresheaf R F`. It uses Mathlib's unique-gluing form
of the sheaf condition. Smooth local sections glue in `F`. The gluing is
smooth: near each point it restricts to one of the smooth local sections, so
`IsLocallyFixedAt.of_restrict` applies. Uniqueness is inherited from `F`.

`smoothSubsheafFunctor R` is the resulting endofunctor of
`TopologicalSheaf G X (ModuleCat R)`. `smoothSubsheafι R` is the natural
inclusion into the identity, and `mono_smoothSubsheafι_app` proves that its
components are monomorphisms. `isSmoothSheaf_smoothSubsheaf` proves that the
smooth subsheaf is smooth.

## The coreflector

`smoothCoreflector R` lifts `smoothSubsheafFunctor R` to the published full
subcategory `SmoothTopologicalSheaf R G X`. For a smooth sheaf `S` and a
morphism `f : S ⟶ F`, `smoothLift` factors `f` through the smooth subsheaf of
`F`, since `f` sends locally fixed sections to locally fixed sections.
`smoothLift_comp_ι` holds by definition. `smoothAdjunction R` is the
adjunction `smoothInclusion R G X ⊣ smoothCoreflector R`. Its hom-set
bijection sends `f` to `smoothLift` and `g` to `g` followed by the inclusion;
all its identities hold by definition. `smoothInclusion_full` and
`smoothInclusion_faithful` record that the inclusion is fully faithful, and
`smoothInclusion_coreflective` packages `Coreflective (smoothInclusion R G X)`.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.4, Definition 1.4.1, printed pp.7–8, defines
the category `T_G(X_ét)` of étale `G`-sheaves, for a topological group `G`, as
the `G_d`-sheaves (sheaves for the discrete group underlying `G`) whose
sections over compact quasi-étale `U` are discrete `G_U`-modules. It is thus a
full subcategory of `G_d`-sheaves. The remark after the definition, printed
p.8, characterizes it by local openness of stabilizers of restricted sections,
which the published `IsSmoothSheaf` transcribes. Worker 13 read these passages
in the original. Sections 1.4 and 1.5 of the manuscript do not construct a
largest `G`-subsheaf of a `G_d`-sheaf. The coreflector here is internal
infrastructure. It is the sheaf analogue of the smooth vectors of a
representation (the published `Langlands.smoothPart`).

On analytic spaces, Berkovich's Key Lemma (printed p.7) provides open
subgroups acting on suitable neighbourhoods. `HasStableNeighbourhoods` is our
own hypothesis replacing it on the ordinary-topological transport site. The
module does not claim that the smooth part is exact, and it does not treat the
analytic étale site.

Source registration:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

All imported modules are present in Library commit
`9a0767626050f3346ad5f25e37cef39f38a5c0dc`.
