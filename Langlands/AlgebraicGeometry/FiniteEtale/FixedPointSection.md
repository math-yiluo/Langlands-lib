# Sections through fixed geometric lifts

For a connected locally noetherian scheme with a geometric point,
an element of a finite étale fibre fixed by the pointed fundamental
group is the value of a section. `sectionOfFixedGeometricLift`
retains the supplied cover and the actual point of its fibre.

The constant map from the fibre of the identity cover to the
supplied point is equivariant by fixedness. The Library's geometric
fibre functor has the Galois category axioms, so fullness of its
functor to finite group actions lifts that equivariant map to a
map of covers. The map from the identity cover is a section and
its effect on the given geometric point is the prescribed lift.

This derived construction is used to recognize rational points
over the strict generic field from trivial monodromy there.
