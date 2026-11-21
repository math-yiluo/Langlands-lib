# Actual unramified fields and their Weil subgroups

For positive `i`, `Numerical.unramifiedStage K i` is the fixed field in the
Library's algebraic closure of `K` of the kernel of the residue-degree map
reduced modulo `i`. The map is continuous and surjective: on the actual
Weil group it reduces integer geometric degree, which takes every integer
value. Its kernel is open, closed and normal. The infinite Galois
correspondence and the quotient by this kernel give a finite Galois
intermediate field of degree `i` without choosing a generator of its residue
field. Absolute inertia lies in the kernel, so the published unramified
criterion gives residue degree `i`; in particular the residue cardinality
is `q_K ^ i`.

The published intermediate-field Weil map has image the pullback of the
fixing subgroup. Consequently it is an open topological embedding and its
image is precisely the Weil elements of degree divisible by `i`. It contains
all of the base Weil inertia. The relative Herbrand slope formula, applied
from index zero with relative inertia index one, makes the inverse Herbrand
function the identity at nonnegative indices. The actual Weil map is
therefore onto each ambient upper ramification group at the same
nonnegative index, and its inverse image of that group is the corresponding
upper group in the stage.

This module constructs the fields and proves the filtration comparisons used
in the proof of route-note Proposition `prop:unram`. Its definition uses the
actual degree kernels, not an abstract choice of fields with the right degree.
It does not assert a Weil-stratum count.
