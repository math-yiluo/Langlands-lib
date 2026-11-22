# Character rigidity for semisimple representations

`equiv_of_character_eq` implements Brauer–Nesbitt for finite-dimensional
semisimple representations of a group over a field of characteristic zero.
Equality of traces on group elements extends by linearity to equality of
traces of all elements of the group algebra. The proof then compares the two
semisimple group-algebra modules over the original coefficient field.

For modules \(M\) and \(N\), the proof decomposes \(M\times N\) into isotypic
components. Projection onto any one component commutes with all module
endomorphisms because the component and the sum of the other components are
fully invariant. The Mathlib surjectivity theorem for the double centralizer
realizes this projection as the action of an algebra element. On each of the
two split summands, that element acts as a projection onto its intersection
with the chosen component. Its trace is the dimension of that intersection.
Equal traces and characteristic zero therefore give equal dimensions.

Each intersection is a direct sum of finitely many copies of the same
simple module. Its dimension determines the multiplicity since a simple
module has positive dimension. Restricting the isotypic decomposition to
each split summand gives a direct-sum decomposition there. The component
isomorphisms combine into a group-algebra linear equivalence, which gives
the required linear intertwiner of representations.
