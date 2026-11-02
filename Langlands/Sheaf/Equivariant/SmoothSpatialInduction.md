# Smooth equivariant sheaves under spatial induction

This module constructs an equivalence between the full categories of smooth
ordinary-open equivariant module sheaves on an `H`-space `X` and on the actual
balanced quotient `G ×_H X`, for an open subgroup `H` of a topological group
`G`. Restriction uses the distinguished unit chart, and its inverse is the
existing genuine right Kan extension. Smoothness of these unchanged sheaves is
proved from actual local fixed-section witnesses.

The content is an internal consequence of `Smooth`, `SmoothPart`,
`SpatialInduction`, `SpatialLocallyConstant`, and the balanced quotient in
`Langlands/Topology/GroupAction/InducedSpace`. It does not introduce an external
comparison theorem as an assumption or assert a new translation from the
literature. The prerequisite modules retain their own provenance.

## Scope and conventions

The ring `R`, group `G`, space `X`, and module carriers all belong to a common
universe `u`. The coefficients are arbitrary modules over a commutative ring;
no coefficient topology or finite-dimensionality is assumed. This follows the
existing smooth-sheaf framework; no comparison across different module universes
is claimed.

The group is a topological group, `H` has the inherited subgroup topology and is
open in `G`, and its action on `X` is jointly continuous. The induced space is
the actual quotient of `G × X` with the relation `[gh,x] = [g,h • x]`, its
constructed quotient topology, and the constructed continuous left `G`-action.
The unit map is `x ↦ [1,x]`.

These constructions do not assume local compactness, total disconnectedness,
normality of `H`, compactness of `X`, a separation property of `X`, or
`HasStableNeighbourhoods`. In particular, importing `SmoothPart` supplies its
fixed-section transport lemma, without invoking its smooth-coreflector
construction or its extra stable-neighbourhood hypothesis.

A transport arrow `f : W ⟶ U` retains its group label `g`, with `g • W ⊆ U`.
The presheaf acts contravariantly. For a subgroup `K` stabilizing an open `V`,
`invariantArrow K V hV k` has label `k⁻¹`; this is the existing convention in
`ActionOpens` and `IsLocallyFixedAt`. Smoothness means that every section near
each point restricts to a section fixed by an open subgroup stabilizing that
neighbourhood. The smooth category is the existing full subcategory, with every
morphism between its objects.

## Local fixed witnesses

`IsLocallyFixedAt.of_map_arrow` applies to any transport presheaf on a space
with continuous constant translations. If `F(f)(s)` is locally fixed at `x`,
then `s` is locally fixed at `g • x`. Given a witness `(V,K)` for the former,
translate `V` by `g` and use the open subgroup obtained as the inverse image of
`K` under conjugation by `g⁻¹`, equivalently `g K g⁻¹`. The translated open is
contained in `U`, since `V ⊆ W` and `f` maps `W` into `U`. The inverse
translation from the translated witness into `V`, followed by its inclusion
into `W` and `f`, is the label-one inclusion into `U`. Applying the presheaf
identifies the two restricted sections. The existing
`map_invariantArrow_map_eq` then proves fixedness under the conjugated subgroup.
No smaller stable neighbourhood must be chosen, which is why this direction
has no stable-neighbourhood premise.

`openSubgroupImage` sends an actual open subgroup `K` of `H` to the subgroup
`K.map H.subtype` of `G`. Its openness is proved using the open embedding of the
open subgroup `H` into `G`. `mem_openSubgroupImage` gives the literal image
membership formula.

`unitPreimage` pulls an arbitrary ambient open back through `x ↦ [1,x]`, and
`unitPreimageArrow` is the actual label-one inclusion of its unit image into
the original ambient open.

`isLocallyFixedAt_of_restrict` sends a unit-chart local witness `(V,K)` to the
ambient witness `(unitOpen V, openSubgroupImage K)`. The quotient identity
`unit(h • x) = h • unit(x)` proves stability. The unit functor preserves the
original labels of the invariant and inclusion arrows, so the fixed-section
equations agree.

`isLocallyFixedAt_restrict` pulls an ambient witness `(V,K)` back to
`W = unitPreimage V` and `L = K.comap H.subtype`. Its neighbourhood stability
again uses the unit identity. The label-one map from `unitOpen W` into `V`
transports the fixed-section equation from `K` to the ambient image of `L`.
Factoring its composite inclusion identifies it with the literal restricted
section on `W`. This proves fixedness under every element of `L`.

`isLocallyFixedAt_restrict_iff` combines the two directions for every section
over a unit-image open and every point of `X`.

## Smoothness and the two functors

`isSmoothSheaf_restrict_iff` proves that the existing spatial restriction
preserves and reflects smoothness. Preservation uses the preceding ambient-to-
unit witness construction. For reflection, represent any point of the quotient
as `[g,x]`, pull the ambient section back along `chartArrow g U`, apply smoothness
of the unit restriction at `x`, lift its witness into the ambient space, and
apply `IsLocallyFixedAt.of_map_arrow`. The resulting witness is at
`g • unit(x) = [g,x]`.

`smoothRestrict` lifts `smoothInclusion ⋙ restrict` into the smooth full
subcategory using this theorem. The object and morphism lemmas identify its
underlying sheaves and maps by reflexivity. `smoothRestrictForgetIso` is the
identity comparison with that original composite functor. Consequently the
construction retains the full sections and all original transport maps; it
never replaces a section module by a selected submodule.

`isSmoothSheaf_induce_iff` proves preservation and reflection for the original
spatial induction. The original isomorphism `restrictInduceIso` identifies the
restriction of an induced sheaf with its source. In each direction its relevant
isomorphism morphism is a monomorphism, so `IsSmoothSheaf.of_mono` transports
smoothness. Combining this with restriction's smoothness equivalence proves the
claim.

`smoothInduce` therefore lifts `smoothInclusion ⋙ induce`, without changing the
underlying right Kan extension. The explicit presheaf and morphism lemmas state
that its underlying presheaf is `unitFunctor.op.ran.obj F.obj.obj` and its map
is `unitFunctor.op.ran.map f.hom.hom`. Its limits are the actual module-category
limits indexed by `StructuredArrow U unitFunctor.op`. The
`unitChartModuleLimits` instance from `SpatialLocallyConstant`, specialized to
the common universe here, constructs these limits from Mathlib's module limits;
no limit-existence hypothesis is added. `smoothInduceForgetIso` is again the
identity comparison with the original composite.

## Full smooth equivalence

`smoothRestrictInduceIso` and `smoothInduceRestrictIso` lift the two existing
ordinary sheaf natural isomorphisms into the smooth full subcategories. Their
components have precisely the old underlying sheaf isomorphisms. Naturality
follows by applying full-subcategory morphism extensionality to the old
naturality equations.

`smoothRestrictionEquivalence` takes `smoothRestrict` as its forward functor
and `smoothInduce` as its inverse. Its unit is the inverse of
`smoothInduceRestrictIso`, its counit is `smoothRestrictInduceIso`, and its
triangle identity is the original spatial equivalence's triangle identity,
viewed in the full subcategory. Both functors are fully faithful and are
registered as equivalences. This establishes an equivalence of the entire
smooth sheaf categories, with genuine inverse natural isomorphisms.

## Remaining boundaries

This unit concerns ordinary-open equivariant module sheaves on actual induced
topological spaces. It does not identify these with analytic or etale sheaves,
construct a smooth coreflector under weaker hypotheses, or supply compact
support, Godement, derived, higher-cohomology, rational-object variation,
arithmetic-tower, or Harris specialization comparisons. Those remain wider-task
obligations. The already constructed ordinary locally constant comparison is a
prerequisite, while its smooth coefficient-natural specialization is subsequent
work.
