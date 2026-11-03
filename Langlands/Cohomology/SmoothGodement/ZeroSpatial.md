# Degree-zero proper smooth Godement maps

This internal construction compares the existing all-degree proper smooth
Godement maps with actual compact-section maps in degree zero. The coefficient
ring, group, spaces and section carriers share universe `u`. The group is
topological, its constant scalar actions on the spaces are continuous, and
both spaces have stable neighbourhoods. Properness is required of the given
continuous equivariant map.

`compactMap_augmentation` proves that the constructed compact chain map
preserves the actual smooth Godement augmentations. It uses the augmentation
equation of `Godement.SmoothSpatial.complexMap` and naturality of the actual
proper compact-section transformation. `cohomologyMap_zero` applies the
augmentation-compatible degree-zero lemma in `EquivariantGodementZeroMap`.
Consequently, the original canonical degree-zero identifications commute with
the all-degree spatial map and the proper compact-section pullback.

`invariantSectionsNatTrans` applies whole-group invariants to that compact
section transformation. Its augmentation equation is the image of the compact
augmentation equation under this functor. `invariantCohomologyMap_zero` then
uses the same general degree-zero lemma with invariant compact sections as
the left exact functor. The order is invariant sections first, module homology
second. No exactness of invariants is assumed.

`coefficientCompactSectionsNatTrans` composes the existing full locally
constant smooth coefficient sheaf map with proper compact pullback.
`coefficientInvariantSectionsNatTrans` restricts it to whole-group invariants.
The two `coefficient…CohomologyNatTrans_zero` theorems give natural
transformation squares for all original smooth coefficient modules and all
intertwiners. Their proofs combine the spatial degree-zero equations with
naturality of the existing degree-zero isomorphisms on the coefficient sheaf
map.

The provenance is internal: the actual maps and identifications already exist
in `SmoothGodement.Spatial`, `CoefficientSpatial`, `CoefficientInvariants`,
`ProperSmoothCompactSections` and `SmoothGodementCohomology`. This file
constructs the section transformations and proves their compatibility with
those maps. It asserts no higher derived comparison, Godement acyclicity,
étale realization or Shimura specialization.
