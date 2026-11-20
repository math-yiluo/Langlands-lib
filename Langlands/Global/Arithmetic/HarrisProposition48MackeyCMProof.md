# CM fields in the arithmetic Mackey step

Harris uses the relative normal closure and its subfields as the ambient fields for the Mackey step in Proposition 4.8, printed pp. 202–203 (`harris-1998-local-langlands`). These lemmas give the CM structures used to give meaning to conjugate inversion and conjugate places in the raw children.

In a totally complex number field, an element that represents the conjugate of a given element under every complex embedding is unique by injectivity. Choosing these representatives for all elements gives an involutive field automorphism. Total complexity makes it nontrivial. Its cyclic subgroup has order two, so the fixed field has index two by the fixed-field degree formula. Every complex embedding of the fixed field extends to an embedding of the larger field. The defining identity of the involution shows that this embedding takes real values on the fixed field, so Mathlib's CM extension criterion applies.

In the relative normal closure, the elements with a conjugate representative under every embedding form an intermediate field. This field contains the image of the CM base and of each base-linear embedding of the larger CM field. These images generate the normal closure, so the criterion proves that the closure is CM.

For an intermediate field over a totally complex base, the Galois correspondence identifies it as the fixed field of its fixing subgroup. Complex conjugation commutes with the automorphisms in that subgroup by `conjQ_central`, so it preserves the intermediate field. Extending each complex embedding of the intermediate field to the ambient CM field proves the conjugate identity on the intermediate field. It is totally complex because it contains the base, so the same criterion gives its CM structure.
