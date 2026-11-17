# Galois descent for noncommutative scalar-extended algebras

This internal helper extends the fixed-tensor argument of
`TensorGaloisPoint.mem_range_includeRight_iff` to a possibly noncommutative
algebra. Its coefficient automorphisms act on the field factor of the tensor
product and fix the algebra factor. In an extended vector-space basis each
coordinate transforms by that field automorphism, so the finite Galois
fixed-field theorem identifies fixed tensors with base-algebra elements.

An algebra equivalence from the scalar extension to its opposite that commutes
with the coefficient action therefore restricts to an algebra homomorphism from
the base algebra to its opposite. The restriction is injective because scalar
extension and the given equivalence are injective. In finite dimension, the
source and its opposite have equal dimension, so this homomorphism is an algebra
equivalence. The construction fixes the base field and makes no assertion of
involutivity.

The provenance is internal. This module supplies the algebra descent step for
the centre-moving norm-one automorphism target, without asserting the group
automorphism classification needed to apply it.
