# Limits and abelian structure for varying-group equivariant diagrams

This module equips the existing category `Langlands.EquivariantDiagram D C`
with limits, colimits and abelian structure inherited from its coefficient
category. It also proves preservation by its existing forgetful and
representation-valued evaluation functors.

The construction is an internal categorical consequence of the implemented
`indexEquivalence` in `EquivariantDiagramCategory`, the published pointwise
preadditive structure in `EquivariantDiagramPreadditive`, and Mathlib's
functor-category, equivalence-transfer and action-category results. There is no
new external-source assertion or Harris comparison theorem.

## Inputs and existence scope

As in the companion category module, `I : Type uI` has morphisms in `Type vI`,
`D : I ⥤ GrpCat.{uG}`, and `C : Type uC` has morphisms in `Type vC`. The group,
base-object, base-morphism, coefficient-object and coefficient-morphism universes
are independent. An auxiliary shape `J : Type uJ` has morphisms in `Type vJ`,
with both shape universes independent of the preceding ones.

`hasLimitsOfShape` and `hasColimitsOfShape` assume the corresponding limits or
colimits of shape `J` in `C`. Mathlib constructs them pointwise in `Index D ⥤ C`;
`Adjunction.hasLimitsOfShape_of_equivalence` and its colimit counterpart transfer
their existence across `indexEquivalence` to the original equivariant category.
Thus this module supplies genuine categorical existence instances for all shapes
available in `C`, without assuming the desired limits of equivariant diagrams.
It does not assert that `C` has arbitrary limits or colimits.

`hasLimitsOfSize` and `hasColimitsOfSize` package this result for independently
specified pairs of shape universes. `hasFiniteLimits` and `hasFiniteColimits`
package the finite-shape consequences. No finite-group or invertible-group-order
hypothesis is used.

## Abelian structure

The instance `Langlands.EquivariantDiagram.abelian` assumes `[Abelian C]` and
proves `Abelian (EquivariantDiagram D C)` by
`CategoryTheory.abelianOfEquivalence` applied to `indexEquivalence.functor`.
Finite products are supplied by the preceding limit construction. The
preadditive structure is the already published one: equivariant natural
transformations have pointwise addition, negation and zero, and composition is
bilinear. The construction transfers the abelian axioms onto this structure;
it does not install a different addition on morphisms.

Mathlib's abelian functor-category instance and its equivalence-transfer
construction discharge the kernel, cokernel and normality obligations. No
abelian property of the equivariant category is supplied as an input.

## Forgetting actions and evaluating

The existing functor

`forget : EquivariantDiagram D C ⥤ (I ⥤ C)`

retains the underlying base diagram and natural transformation. `forgetIndexIso`
constructs its natural isomorphism with

`toFunctor ⋙ (Functor.whiskeringLeft I (Index D) C).obj Index.inclusion`.

The component is obtained by forgetting the equivariant recovery isomorphism
`fromToIso`. Its underlying component at each base index is an identity.

`forget_preservesLimitsOfShape` assumes `[HasLimitsOfShape J C]` and proves
preservation of shape `J` by `forget`. The equivalence functor preserves limits,
and precomposition along the base inclusion preserves them by Mathlib's
`whiskeringLeft_preservesLimitsOfShape`. Preservation transfers through
`forgetIndexIso`. `forget_preservesColimitsOfShape` gives the dual construction
under `[HasColimitsOfShape J C]`.

For each `i : I`, the existing functor

`evaluation i : EquivariantDiagram D C ⥤ Action C (D.obj i)`

retains the action at that index. `evaluation_preservesLimitsOfShape` and
`evaluation_preservesColimitsOfShape` prove its preservation under the same
shape-existence assumptions on `C`. After forgetting the target action, the
composite is `forget` followed by ordinary functor evaluation. These functors
preserve the relevant limits or colimits; Mathlib's action forgetful functor
reflects the required universal properties. The proofs use
`Action.preservesLimitsOfShape_of_preserves` and its colimit counterpart.

The final four instances package finite-limit and finite-colimit preservation
for `forget` and for every action-valued `evaluation i`, assuming the
corresponding finite limits or colimits in `C`.

## Remaining specialization

For abelian `C`, this provides the source abelian category and preservation
certificates needed for later homological constructions. This module does not
construct the varying-cover associated-sheaf functor's exactness, its homology
comparison, or any compact-support, global-section, inverse-limit or derived
cohomology comparison. Actual geometric torsors and Shimura specializations
remain separate inputs and construction obligations. These purely algebraic
diagram categories impose no smoothness or topological continuity condition.
