# Spatial induction of equivariant sheaves along an open subgroup

This module constructs the equivalence between all ordinary-open `H`-equivariant
sheaves on `X` and all ordinary-open `G`-equivariant sheaves on the actual
balanced quotient `G ×_H X`. Its restriction functor evaluates an ambient sheaf
on the unit-chart image of each open of `X`. Its induction functor is a genuine
right Kan extension, and both inverse isomorphisms are constructed.

The namespace is `Langlands.Sheaf.Equivariant.SpatialInduction`. The entry
construction is `restrictionEquivalence`.

## Provenance and scope

This is internal content derived from the published
`Langlands.Sheaf.Equivariant.Site` and
`Langlands.Topology.GroupAction.InducedCharts` constructions and Mathlib's
dense-subsite comparison theorem. It makes no new original-literature claim.
The proof below derives the comparison hypotheses from the actual quotient,
charts and group-labelled arrows; a desired sheaf equivalence is never an input.

The sheaves here are the published `TopologicalSheaf` objects: presheaves on the
transport category whose restriction to ordinary open inclusions is a sheaf.
Their morphisms commute with every restriction and group transport. Smoothness,
compact sections, Godement and derived comparisons, analytic or etale sheaves,
and arithmetic/Harris specialization remain separate obligations. In particular,
this is spatial induction to a different space, rather than induction of
equivariance on an unchanged space.

## Parameters and size assumptions

The declarations use independent universes:

- `G : Type v` is a group and a topological group.
- `H : Subgroup G` is open, with the inherited subgroup topology.
- `X : Type u` is a topological space with a continuous `H` action.
- `A : Type a` is a coefficient category with morphisms in universe `b`.

Restriction and its full and faithful instances require no coefficient limits.
To construct induction and the equivalence, the module explicitly requires
`HasLimitsOfShape (StructuredArrow U (unitFunctor H hH X).op) A` for every
`U : (ActionOpens G (Space H X))ᵒᵖ`. These are the actual limits defining the
pointwise right Kan extension; the hypothesis is a coefficient-category
completeness condition, not an assumed geometric comparison. The independent
coefficient universes are retained, and the needed limits are not silently
inferred for a category too small to possess them.

No normality, local compactness, total disconnectedness, compactness of `X`,
coefficient topology or stable-neighbourhood hypothesis is imposed.

## The unit-chart functor

`Space H X` is the existing balanced quotient of `G × X`, with relation
`[g h,x] = [g,h • x]`, and actual left `G` action. Write
`unit(x) = [1,x]` and `chart(g,x) = [g,x]`.

For an `H` transport open `U`, `unitOpen` has underlying open `unit '' U`.
Openness follows from the published open-embedding theorem for the unit chart;
`mem_unitOpen` uses the injectivity of that chart. The functor `unitFunctor`
sends an arrow with label `h : H` to the arrow with label `(h : G)`. Its
well-definedness is the actual balanced relation
`unit(h • x) = h • unit(x)`. Identities and composition retain their labels.

`unitFunctor_faithful` follows from subgroup inclusion and extensionality by
labels. Fullness is not asserted: an arrow from an empty open may have an
ambient label outside `H`.

`mem_subgroup_of_smul_unit_eq` proves that `g • unit(x) = unit(y)` forces
`g ∈ H`. Applying the actual component map to `G ⧸ H` gives equality with the
unit coset. The theorem is algebraic; it omits unused topology assumptions.
`liftArrow` lifts any arrow between unit-chart opens whose label lies in `H`,
and `unitFunctor_map_liftArrow` proves that it maps back to the original arrow.
`label_mem_of_mem` obtains this subgroup membership from any point in the
source open.

`unitFunctor_locallyFull` uses that lift wherever the source has a point.
For each such point, the identity arrow belongs to the pushed-forward image
sieve and covers that point. If the source is empty, the pointwise cover
condition has no points to check. Faithfulness supplies local faithfulness by
Mathlib's general instance. Thus empty opens are handled by the topology,
without discarding their transport arrows or claiming global fullness.

## Dense-subsite proof

The transport topology is the published topology whose covering sieves have
translated arrow-images covering every point. The proof uses its theorem
`mem_transportTopology_iff_exists_smul` in both directions.

`chartPreimage g V` is the open inverse image of the ambient open `V` along the
continuous actual chart `x ↦ [g,x]`. `chartArrow g V` has label `g` and sends the
unit image of this inverse image into `V`.

For any `z ∈ V`, choose an actual quotient representative `z = [g,x]`. Then
`x` belongs to `chartPreimage g V`, and `chartArrow g V` sends `unit(x)` to `z`.
This arrow factors through an object in the image of `unitFunctor`, so it
belongs to `Sieve.coverByImage`. This proves `unitFunctor_coverDense` for every
ambient open, not only whole components or invariant opens.

`unitFunctor_pushforward_mem_iff` proves that a sieve `S` on an `H` transport
open covers exactly when its pushforward along `unitFunctor` covers. To reflect
a cover, cover `unit(x)` by an ambient arrow `f` in that pushforward. By the
pushforward definition, write `f = k ≫ j(i)`, with `S(i)` and
`k : V ⟶ j(W)`. A preimage point `v` is taken by `k` to `unit(y)` with `y ∈ W`.
The label-composition law and the balanced relation give
`unit(i.label • y) = f.label • v = unit(x)`. Unit-chart injectivity implies
`i.label • y = x`, producing an original covering arrow of `S`. To preserve
a cover, map each original arrow and its preimage point into the unit chart.
The factorization with an identity arrow proves membership in the pushforward.

`unitFunctor_denseSubsite` combines cover density, local fullness, local
faithfulness and this cover equivalence. Mathlib then proves continuity and
cocontinuity, and that restriction on transport sheaves is full and faithful.

## Restriction, induction and inverse maps

`restrict` composes the published equivalence from ordinary-open equivariant
sheaves to transport-site sheaves, Mathlib's restriction by precomposition
with `j.op`, and the inverse published equivalence for the subgroup. Here
`j = unitFunctor H hH X`. Its underlying presheaf is literally `j.op ⋙ F.obj`.
The evaluation lemmas record:

- At an open `U`, the object is `F(unit '' U)`.
- At an arrow `f`, the map is `F.map (j.map f).op`.
- A morphism of ambient sheaves restricts to its original component at
  `unit '' U`.

`restrict_full` and `restrict_faithful` hold for every coefficient category.
They use the dense-subsite result and the published transport-site
equivalences, retaining all original equivariant morphisms.

Under the stated limits, `induce` is the same composition in the other
direction with `j.op.ran`. The underlying presheaf is literally
`j.op.ran.obj F.obj`; its morphism map is literally `j.op.ran.map f.hom`.
At an ambient open `V`, this is the limit over
`StructuredArrow (op V) j.op` of the original values `F(U)`. An object of this
index category is an actual transport arrow `j(U) ⟶ V`. Mathlib's
cocontinuity theorem proves that this right Kan extension is a sheaf.

`restrictionEquivalence` composes the two published transport-site
equivalences with `sheafAdjunctionCocontinuous.toEquivalence`. Mathlib's
dense-subsite comparison proves that the unit and counit of this genuine
restriction/right-Kan adjunction are isomorphisms under the explicit limits.
`restrictionEquivalence_functor` and `restrictionEquivalence_inverse` identify
its functor with `restrict` and its inverse with `induce` by reflexivity.
The module also exposes `restrict_isEquivalence` and `induce_isEquivalence`.

`restrictInduceIso : induce ⋙ restrict ≅ 𝟭` is the counit isomorphism and
recovers the full subgroup-equivariant sheaf. The inverse unit isomorphism
`induceRestrictIso : restrict ⋙ induce ≅ 𝟭` recovers the full ambient
`G`-equivariant sheaf. These are natural isomorphisms of actual functors with
all equivariant sheaf morphisms; neither inverse law is supplied as data.
