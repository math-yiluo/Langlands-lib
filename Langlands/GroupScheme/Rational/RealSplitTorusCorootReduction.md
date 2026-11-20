# The split torus image from fixed absolute coroots

This internal reduction combines the integral involution decomposition, the
affine torus norm and actual cocharacter evaluation. It is part of the proof
of connectedness of real points of a simply connected group.

The reduction takes a real torus homomorphism into the ambient group, a
root datum with spanning coroots on the actual lattices of its split
complexification, and a split subtorus over the reals. Its remaining hypothesis is
that the value at minus one of each fixed simple coroot belongs to the
scalar extension of the real identity component. The supplied root-datum
automorphism acts on cocharacters by ordinary complex conjugation. Its
square acts trivially, as required by the lattice lemma.

Evaluation at minus one in the complex torus is multiplicative on sums of
cocharacters. After mapping to the ambient complex points, the preimage of
the extended real identity component is an integral submodule of the
cocharacter lattice. It contains the fixed simple coroots by hypothesis.
It contains every cocharacter norm because its value is the scalar extension
of the torus point norm. The complex point norm expands into the product of
the identity and conjugation terms, and minus one is fixed by conjugation.

Any real cocharacter of the torus extends to an invariant complex
cocharacter. The lattice decomposition puts it in this submodule, yielding
identity-component membership for the value at minus one by injectivity of
scalar extension. A positive real unit is a square and its cocharacter
value is a real torus norm. A negative real unit is minus one times such
a square. The rational points of the split subtorus are products of these
real cocharacter values, so their images lie in the real identity component.
