# The split quotient of a torus determined by invariant characters

Worker 714. Internal construction for the anisotropic part.

For a torus split by a finite Galois extension, its integral character lattice
is finite free. Its invariant submodule is finite free over the integers.
Choosing a basis gives a split torus over the original field. The inclusion
of its geometric characters into the original torus characters is equivariant,
so finite Galois character descent produces an actual homomorphism to this
split torus. Its character pullback is injective with image exactly all the
invariants. The preliminary lemma records that every geometric character of
a ground-field split torus is Galois fixed.

`SplitQuotientData` packages the actual quotient, its homomorphism, splitness,
injectivity of geometric pullback, and its image equality. `splitQuotient`
chooses such data from the proved existence theorem. These constructions use
no anisotropic-subtorus or product-decomposition hypothesis.
