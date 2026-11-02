# The Zariski sheaf of general relative rigidified classes

`openCoverOver` regards an actual open cover of the underlying test scheme as
a family in the slice category. The general helper
`isSheaf_zariski_over_of_openCover` states that unique gluing for every such
family gives the sheaf condition for the big Zariski topology on that slice.
It applies to any type-valued presheaf, without changing its values or maps.

The proof chooses an actual open cover contained in the underlying covering
sieve. The corresponding slice cover generates a subsieve for which the
presheaf is a sheaf by hypothesis. Pulling that open cover back along an
arbitrary slice map gives a cover contained in the pullback sieve; unique
gluing on this cover proves separation on that sieve. Mathlib's subsieve
criterion then gives the sheaf condition on the original covering sieve.

`RigidifiedLineBundle.classPresheaf_isSheaf_zariski_of_unique` applies this
criterion to the published presheaf of actual relative rigidified classes.
Its input is uniqueness of rigidified isomorphisms over every test scheme,
for arbitrary `f`, its section `ε`, and the section law. A compatible family
on a slice cover gives exactly the pairwise overlap equations required by
`classes_zariskiGluing_of_unique`; this theorem supplies a global class.
`classes_zariskiSeparated_of_unique` supplies uniqueness of that class.
The resulting conclusion is the type-valued `Presieve.IsSheaf` condition
for `Scheme.zariskiTopology.over S`, with the published pullback coherence.

This is derived internal content combining the general separation and gluing
modules with the pinned Mathlib definitions of induced slice topologies and
covering sieves. It proves neither the explicit isomorphism-uniqueness input
nor the fppf sheaf condition or the final Picard comparison.
