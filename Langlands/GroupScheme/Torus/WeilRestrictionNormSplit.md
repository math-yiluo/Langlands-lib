# Scalar and norm morphisms in splitting coordinates

This internal construction compares the published scalar and determinant norm
morphisms of `WeilGm` with a chosen algebra decomposition. All types lie in one
universe. No new structural theorem from the literature is an input.

For commutative rings `A`, `A'`, `B` and `R`, an `A'`-algebra equivalence
`e : A' ⊗_A B ≃ (I → A')`, and a finite index type `I`,
`normDecompositionEquiv` gives the induced `R`-algebra equivalence
`R ⊗_A B ≃ (I → R)`. Here `R` is an `A'`-algebra with the displayed compatible
`A`-algebra structure. It uses cancellation of iterated tensor base change,
extension of `e`, and the finite product tensor equivalence.
`normDecompositionEquiv_comm` compares it with the published coefficient-last
`decompositionTensorEquiv` on pure tensors and then by tensor induction.
The companion `TensorNormSplit` computes the determinant norm in a product
algebra; transporting that formula proves `tensorNorm_decomposition`.

For the actual group-scheme comparisons, `B` is finite free over `A`, `A'` is
an arbitrary commutative `A`-algebra, and `e` is as above.
`decompositionNormHom` is the base change of the published norm character,
followed by the canonical base-change comparison for the multiplicative group.
`decompositionScalarHom` is the base change of scalar inclusion, preceded by
the inverse multiplicative-group comparison. Their all-test formulas are:

- `decompositionNormHom_points`: the norm is the product of all splitting
  coordinates.
- `decompositionScalarHom_points`: scalar inclusion sends a unit to the
  constant tuple with that value.

Both formulas quantify over every scheme over `Spec A'`, including nonaffine
and nonreduced schemes. The proofs use the published base-change point
comparison, scalar/norm unit formulas, and the induced tensor decomposition.
They require no field, injectivity, reducedness or nonzero-ring assumption.
Finite freeness is retained for these group-scheme comparisons; the underlying
published scalar morphism alone has the broader finite-projective scope.

Over a coefficient field `K`, with any `A`-algebra structure and decomposition
`K ⊗_A B ≃ (I → K)`, the actual character and cocharacter equivalences from
`WeilRestrictionDecomposition` identify the norm character and scalar
cocharacter with the function `i ↦ 1`. These are
`decompositionCharacterEquiv_normHom` and
`decompositionCocharacterEquiv_scalarHom`. The proofs compare actual morphisms
on all tests using the published monomial formulas. Consequently,
`decomposition_latticePairing_normHom` pairs a cocharacter with the norm by
summing its coordinates, and `decomposition_latticePairing_scalarHom` pairs a
character with scalar inclusion by summing its coordinates. The pairing
identities follow from the published dot-product comparison.

These are intrinsic comparisons of the existing constructions. Applying them
to the published finite-separable embedding decomposition gives the usual
embedding coordinates. This file does not construct or identify norm kernels,
or prove a classification of subtori.

Author: Worker 207.
