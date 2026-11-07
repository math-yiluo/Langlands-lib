# Actual matrix adjoints on the archimedean place Lie factors

For any field `F : Type u` and natural rank `n`, this module compares the
original global archimedean adjoint with actual matrix conjugation at each
infinite place. All ranks, including zero, are allowed, and no number-field
hypothesis is required for this algebraic construction.

`unitaryMatrixRealLieConjugation` constructs a real Lie automorphism of
`Matrix (Fin n) (Fin n) 𝕜` for an actual unitary matrix `k`, with
`𝕜 : Type v` any `RCLike` field in an independent universe. Its formula
is `k.val * X * k⁻¹.val`. The inverse conjugates in the reverse direction.
The units associated to the actual unitary matrix prove the inverse and
multiplication identities. Conjugation preserves addition and real scalar
multiplication and preserves the ordinary matrix commutator.

`unitaryMatrixComplexLieConjugation` extends this entire underlying real
matrix Lie algebra and its conjugation by complex scalars. Its domain is
`ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕜`. In particular, at a complex place
both real directions are retained before complexification. The pure tensor
formula is the identity on the first scalar factor and the actual real
matrix adjoint on the second.

`realProjection_realLieConjugation` and
`complexProjection_realLieConjugation` compute the actual global real
adjoint under each existing place projection. The projected result is the
matrix of the group element, multiplied by the projected Lie direction,
then by the matrix of the inverse group element. These identities follow
by applying the existing matrix algebra projection to the published global
matrix adjoint identity and preserving multiplication.

`realLieConjugation_realInclusion` and
`realLieConjugation_complexInclusion` show that conjugation by any full
compact coordinate product preserves each actual place-supported Lie
inclusion. Its effect in that place is the actual adjoint of the compact
matrix in that coordinate. The proof uses the original real Lie coordinate
equivalence and checks each real and complex projection. At the selected
coordinate it is exactly matrix conjugation. At all other coordinates
the inserted Lie direction is zero, so conjugation gives zero. Opposite
types of place also give zero. No invariant-subspace premise is supplied.

The two `complexLieConjugation_*Inclusion` identities extend these actual
insertion compatibilities to all complexified Lie directions. Tensor
induction reduces to the proved real identity on pure tensors and
linearity on sums.

This is an internal construction from `ArchimedeanAdjoint`,
`ArchimedeanPlaceLie`, `ArchimedeanPlaceCompact`, and pinned Mathlib's actual
unitary-to-units and scalar-extension constructions. It uses no new
original-literature assertion, topology or normalization. It does not
construct irreducible automorphic components or a Langlands attachment.
