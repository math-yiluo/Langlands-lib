# Line bundles on the relative space of a coproduct chart

Module: `Langlands.AlgebraicGeometry.Picard.CoproductChartLineBundle`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This is an internal construction with no literature assertion. It glues
actual line bundles on the members of an open cover whose distinct members
do not meet, and applies this to the relative space `U ×ₛ X` of a coproduct
chart `U = ∐ᵢ Vᵢ` over `S`. It is a step in assembling a Picard-stack atlas
from charts at single points (Stacks Lemma 98.17.1, Tag 07Y4, takes the
coproduct of such charts). All schemes and index types are in one universe
`u`.

## Gluing on a disjoint open cover

For a scheme `Y` and an open cover `𝒰 : Y.OpenCover`,
`DisjointCoverGluing.IsDisjoint 𝒰` says that for distinct indices `i ≠ j`
the scheme pullback of `𝒰.f i` and `𝒰.f j` is empty.

- `modules_hom_ext`: two morphisms of module sheaves on an empty scheme are
  equal, since all section modules are zero.
- `isoOfIsEmpty`: any two module sheaves on an empty scheme are isomorphic,
  by the zero morphisms.
- `diagTransition i M`: on the self-overlap `𝒰.X i ×_Y 𝒰.X i` the two
  projections are equal because `𝒰.f i` is a monomorphism. The
  identification of the two pullbacks of `M` is the published
  `CommonSourceCocycle.transition` with `M` itself as common source over
  `𝒰.X i` and identity maps.
- `transition h M i j` is `diagTransition` when `i = j` and `isoOfIsEmpty`
  on the empty overlap otherwise; `transition_self` records the first case.
- `cocycle`: these identifications satisfy the published module-gluing
  cocycle condition `OpenCoverModuleGluing.CocycleCondition`. If the three
  indices agree, this is `CommonSourceCocycle.transition_cocycle`. Otherwise
  the triple overlap maps to an empty pairwise overlap, so it is empty and
  the condition holds by `modules_hom_ext`.
- `gluingData h L`, `glue h L`, `glueIso h L i`: for line bundles `L i` on
  the members, the published `LineBundleGluingData` gives a line bundle on
  `Y` together with isomorphisms between its pullback to each member and
  `L i`.

## The relative space of a coproduct chart

Fix `f : X ⟶ S` and a family `V : ι → Over S`, with coproduct
`AlgebraicSpace.CoproductChart.sigmaOver V` and inclusions `sigmaOverι V i`.

- `isPullback_relativeSpace_map`: for a map `h : T ⟶ U` over `S`, the square
  formed by `(relativeSpace f).map h`, the two first projections and
  `h.left` is a pullback square (pasting with the defining pullback squares
  of `T ×ₛ X` and `U ×ₛ X`).
- `relativeCover f V`: the open cover of
  `(relativeSpace f).obj (sigmaOver V)` whose members are the relative
  spaces `(relativeSpace f).obj (V i)` and whose maps are
  `(relativeSpace f).map (sigmaOverι V i)`. It is Mathlib's pullback of
  `sigmaOpenCover` along the first projection, with each member replaced by
  the isomorphic relative space through the pullback square above
  (`Scheme.Cover.copy`). `relativeCover_f` and `relativeCover_X` are its
  definitional values.
- `relativeCover_isDisjoint`: distinct members do not meet, since their
  overlap maps to the overlap of two distinct coproduct inclusions, which is
  empty by Mathlib's `isEmpty_pullback_sigmaι_of_ne`.
- `bundle f V L`: for line bundles `L i` on the relative spaces of the
  components, the line bundle on the relative space of the coproduct glued
  from them.
- `bundleIso f V L i`: an isomorphism between the pullback of `bundle f V L`
  along `(relativeSpace f).map (sigmaOverι V i)` and `L i`.

No hypothesis on `f`, `S` or the family is needed.
