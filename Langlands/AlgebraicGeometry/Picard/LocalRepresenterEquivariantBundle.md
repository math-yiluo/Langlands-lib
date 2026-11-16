# Equivariant universal bundle of a local presheaf representer

This internal construction equips the actual local universal bundle with
coherent transport along the étale equivalence relation of a supplied local
representer. It retains independent scheme and value universes.

`related_base` identifies the original-base coordinates of related chart
maps, and `related_family` proves equality of their classified families on
the common test scheme. `equivariantBundle` then uses the actual transitions
of `PresheafLineBundle` to construct `EquivariantLineBundle`. The identity,
transitivity and precomposition laws come from the corresponding transition
laws, with slice maps identifying the test schemes' base coordinates.

The bundle on the chart is exactly the universal bundle of the base-restricted
presheaf line bundle. The companion `PresheafLineBundleCocycle` helpers derive
transition naturality from the existing cartesian composition axiom; this
candidate supplies the actual equivariant-bundle construction they support.
No quotient or effective descent is asserted.
