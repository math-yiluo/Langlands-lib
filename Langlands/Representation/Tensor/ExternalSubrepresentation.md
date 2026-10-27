# Actual invariant subspaces in an external tensor slot

This internal algebraic adapter constructs the invariant tensor subspace
obtained from a supplied subrepresentation in any original factor.

`Langlands.FiniteTensor.externalSlotSubrepresentation ρ j S` first pulls the
action on `S` through the original coordinate homomorphism. It tensors this
invariant subspace on the left by the complementary tensor, using the actual
image of the subspace inclusion, and pulls that image back through the
original slot splitting equivalence. Thus its ambient representation is
exactly `FiniteTensor.external ρ`. Bottom and top subrepresentations are
preserved.

For a finite index type with nonzero complementary factor carriers,
`externalSlotSubrepresentation_le_iff` proves that the construction reflects
and preserves inclusion. To obtain a nonzero complementary tensor vector, the
proof uses the tensor product of vector space bases and a basis element in
each complementary factor. This also covers an empty complement.

The supporting theorem
`Langlands.TensorFiltration.leftTensorImage_le_iff` proves reflection of
inclusion after tensoring with any nonzero vector space. A linear functional
taking value one on a fixed nonzero tensor-factor vector gives a contraction.
The contraction sends the tensor image of an invariant subspace back into
that subspace, as verified on pure tensors and sums. Applying it detects the
original subspace inclusion. The converse is the existing monotonicity of
the tensor image.

`externalSlotSubrepresentation_ne_bot` and
`externalSlotSubrepresentation_ne_top` follow by applying inclusion
reflection and the two endpoint identities. Consequently a proper nonzero
subrepresentation remains proper and nonzero when the stated complementary
carriers are nonzero. The nonzero hypotheses are essential.

The coefficient field, index, group, and carrier universes are independent.
The slot construction and endpoint identities allow arbitrary index types;
the inclusion-reflection and strictness results assume a finite index type.
No smoothness, simplicity, admissibility, or dimension assumption occurs.

Provenance is internal assembly of `Tensor.FiniteFiltration`,
`Tensor.Filtration`, `LengthTwo.comap`, and Mathlib's tensor product,
vector space basis, and projective-module dual functional APIs. This module
asserts no classification or parabolic-induction result.
