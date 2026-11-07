# Actual matrix adjoints on two-place enveloping tensor algebras

`unitaryMatrixEnvelopingTensorConjugation` constructs the complex algebra
automorphism of the tensor product of two entire matrix universal
enveloping algebras induced by the two supplied unitary matrices. The two
RCLike coefficient fields have independent universes, and the two ranks
are independent natural numbers. Each Lie algebra is the complexification
of the full underlying real matrix Lie algebra. The tensor product is
over the complex numbers.

The construction applies Mathlib's `Algebra.TensorProduct.congr` to the
two actual `unitaryMatrixEnvelopingConjugation` equivalences. Its
pure-tensor formula applies each matrix adjoint to its respective factor.
Identity matrices induce the identity; simultaneous matrix multiplication
induces composition in the order for conjugation by the product; inverses
induce the inverse equivalence. These laws follow from the corresponding
proved single-factor laws and the tensor congruence laws.

For an arbitrary field `F : Type u` and every natural rank, each actual
two-place tensor algebra map into the global enveloping algebra commutes
with global compact conjugation and this tensor adjoint of the selected
coordinate matrices. The identities hold as equalities of algebra
homomorphisms and on every tensor element. The real/real and
complex/complex maps retain the inequality of places; the mixed map uses
one place of each type. No number-field hypothesis is needed.

Tensor algebra homomorphism extensionality reduces each equality to pure
tensors. The actual tensor-map product formula, multiplication
preservation and the proved whole-local inclusion covariance establish
that case. Evaluating the equality gives the all-element formulas.

This is an internal construction from
`ArchimedeanPlaceEnvelopingAdjoint`, `ArchimedeanPlaceEnvelopingTensor`
and the pinned Mathlib tensor-product equivalence API. It makes no new
original-literature assertion and introduces no topology or
normalization. It supplies neither injectivity of the two-place tensor
maps nor a tensor decomposition of a representation, irreducible local
factors, admissibility or Langlands attachments.
