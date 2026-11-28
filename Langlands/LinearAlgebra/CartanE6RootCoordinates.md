# Integral coordinates of the roots of type E₆

The coordinate list uses the simple basis numbered by `CartanMatrix.E 6`.
The first six vectors are its simple roots. Each later vector is the reflection
of an earlier one in a simple root, as certified by its parent and reflecting
vertex. Every simple reflection sends a listed vector to a signed listed
vector. The Lean proof verifies these finite assertions and uses induction by
simple reflections in a reduced based root datum. Thus every root of the actual
datum is represented by a signed entry of the list, and every listed vector
represents an actual root.
