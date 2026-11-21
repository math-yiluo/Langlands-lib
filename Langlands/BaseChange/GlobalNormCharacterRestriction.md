# Characters of the global norm quotient and their finite restrictions

For a cyclic extension of number fields, `GlobalNormCharacterRestrictionStatement` gives
an injective family of Hecke characters indexed by the complex characters of the Galois
group. Its image consists of the Hecke characters whose pullback by the idele class norm
is trivial. The indexing group has cardinality the degree. At a finite place, restriction
to the lower completion gives all characters trivial on the norms from an upper completion.
Each such restriction occurs as many times as there are places above the lower place.
This includes split places and places where the local degree is greater than one.

The proof pulls the finite Galois characters back along the global norm quotient map.
Surjectivity gives injectivity of this family. The kernel equality descends any
norm-trivial Hecke character to the finite Galois group. At a finite place, the character
restriction is composition with the finite component of the quotient map. Finite abelian
duality and its kernel and image identify the restrictions and the number of extensions.
The decomposition group has order equal to the local degree. The Galois place count
identifies its index with the number of upper places.

This is the character indexing used in the auxiliary factor comparison of Arthur–Clozel,
Chapter 1, (6.2), (6.17), and Lemma 6.13. The idelic norm quotient and its local kernels are
proved in the accompanying `GlobalNormReciprocity` module.
