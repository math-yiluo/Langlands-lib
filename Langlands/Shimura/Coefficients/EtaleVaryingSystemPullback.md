# Etale base change of full varying-torsor coefficient systems

This internal construction compares restriction of a whole varying-group
associated-sheaf system with the associated system formed independently on the
actual base-changed finite geometric torsors. It includes the coefficient
reductions and the inverse cover-comparison maps in every transition.

## Parameters and genuine geometric input

The schemes `X`, `Z`, coefficient ring `R`, module carriers and deck-group
carriers share universe `u`. The indexing category has independent object and
morphism universes `uI`, `vI`. The morphism `f : Z ⟶ X` is etale.

For `D : I ⥤ GrpCat`, the cover diagram
`Y : EquivariantDiagram D X.Etale` is supplied with the genuine condition
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`. This means a finite deck
group, finite surjective structural morphism, and a unique deck transformation
between any two points over the same base point over every separably closed
field in universe `u`. No comparison is assumed as input. Each coefficient
diagram `M : EquivariantDiagram D (ModuleCat R)` is
arbitrary; there is no finiteness or invertibility hypothesis on its modules
or on the coefficient ring.

The pulled-back cover diagram is exactly
`(etaleTorsorDiagramPullback f D).obj Y`. Its objects are actual scheme fiber
products, with induced deck actions and geometrically pulled-back transition
maps. The already proved
`etaleTorsorDiagramPullback_isFiniteGeometricTorsor` supplies its torsor
condition. The original group and coefficient diagrams are retained.

## Transition comparison

`etaleAssociatedTransition_pullback` proves, for every `b : i ⟶ j` and
coefficient diagram `M`,

```text
restriction f (transition_b) ≫ q_j
  = q_i ≫ transition'_b.
```

Here `q_i` is the forward `etaleConstantAssociatedPullback` component at cover
`Y.action i` and representation `M.action i`. The transition on either side is
the existing coefficient-reduction leg followed by the inverse of the actual
cover-comparison isomorphism.

The implemented proof cancels the base-changed cover-comparison map, whose
invertibility is the previously proved finite-geometric-torsor comparison
theorem. The cross-cover pullback square rewrites the remaining comparison
factor. Functoriality of restriction and
`etaleAssociatedTransition_comparison` then reduce the equation to the proved
coefficient-reduction square. Thus compatibility with the actual inverse
transition follows from the two already constructed cospan legs.

## Whole natural isomorphism

`etaleAssociatedVaryingSystemPullback` constructs

```text
etaleAssociatedVaryingSystemFunctor X Y hY ⋙ postcompose (restriction f)
  ≅ etaleAssociatedVaryingSystemFunctor Z
      ((etaleTorsorDiagramPullback f D).obj Y) pulledBackTorsorCondition.
```

At a coefficient diagram `M` this is an isomorphism of `I`-indexed sheaf
diagrams. Its naturality in index arrows is exactly the transition comparison.
Its naturality in every coefficient-diagram morphism follows indexwise from
`etaleAssociatedAtPullback`. The forward and inverse component lemmas identify
both maps with the corresponding canonical constant-associated components.
`etaleAssociatedTransition_pullback_inv` records the naturality equation for
the inverse system map. Consequently the complete diagram, including its
identity and composition laws, is transported.

## Provenance and boundaries

This is derived internal infrastructure from `VaryingCoverInverse`,
`EtaleVaryingCoverPullback`, their actual geometric and invariant-sheaf
prerequisites, and Mathlib's natural-isomorphism constructor. The torsor
comparison theorem is imported as a proved result; it is not an added axiom or
an output hypothesis. No additional theorem of Harris is claimed here.

This unit compares ordinary associated sheaf diagrams under one etale base
change. Compatibility between successive geometric base changes, arbitrary
non-etale inverse image, particular Harris level schemes and their torsors,
compact supports, inverse limits and cohomological comparison maps remain
separate constructions.
