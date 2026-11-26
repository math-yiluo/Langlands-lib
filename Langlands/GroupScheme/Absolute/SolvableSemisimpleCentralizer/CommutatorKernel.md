# The commutator and fixed subgroup of semisimple conjugation

For a normal commutative subgroup, the commutator with a fixed section is a
group endomorphism with kernel the centralizer inside that subgroup. If the
subgroup is unipotent and the section is semisimple, the commutator image and
kernel meet on rational points only at the identity. Indeed, a commutator in
the kernel is a commuting unipotent factor relating the section to an inner
conjugate of itself, so Jordan uniqueness forces that factor to be trivial.

Images of the iterates form a descending chain of closed subsets in a
Noetherian space. Stabilization and the equality of the rational kernels of
the commutator and its square give the rational-point product of the image
and kernel. The corresponding group homomorphism from their product has
connected kernel, since that kernel has only the identity rational point.
Connectedness of the original commutative group then gives connectedness of
the product and of its projection onto the commutator kernel.

This implements the commutator step of Milne, *Algebraic Groups* (2017),
Lemma 16.39, printed p. 338. The retained source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
