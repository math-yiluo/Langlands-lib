# Integral coroot coordinates of the actual odd maximal torus

This file defines the coordinate characters and cocharacters of the
actual split torus and computes the coroots attached by any actual root
datum of its maximal identity torus. A short root `e_a` has coroot
`2 e_a^vee`; a long root `e_a-e_b` has coroot `e_a^vee-e_b^vee`.

All coordinates of a computed actual root lie between minus one and one.
Apply this bound to integral reflections of the short coordinate roots
and the coordinate sums and differences. The root-coroot self-pairing
is two. For a short root this fixes its own coordinate at two, and bounds
on the reflected adjacent long roots force every other coordinate to
vanish. For a difference long root, reflections of its two short
coordinate roots force the two coroot coordinates to be one and minus
one; reflecting long roots involving each remaining coordinate forces
that coordinate to vanish.

These are integral lattice calculations through the actual root-datum
reflection, without evaluating characters or coroots in the field.
They therefore retain all characteristics, including two. The content
is an internal consequence of the computed actual roots and root-datum
axioms, with no new source translation or presentation premise.

The signed-coordinate basis uses the split-torus `SymplecticMatrix.coordChar` and `coordCochar`.
