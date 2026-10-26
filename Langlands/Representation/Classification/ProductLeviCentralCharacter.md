# Full central characters of product Levi representations

This internal construction supplies the central-character reduction needed for
the analytic temperedness of actual opposite Jacquet constituents. It does not
establish an analytic estimate or assert that unitary central character implies
temperedness.

For a block shape `B` and a commutative ring `R`,
`GeneralLinear.BlockShape.blockScalarToCenter` sends a tuple of units to its
block-scalar matrix, with its certificate of membership in the entire center of
`B.Levi R`. The existing `blockScalarLevi_mem_center` proves centrality.
`blockScalarToCenter_bijective` proves injectivity by evaluating each block and
using `GeneralLinear.scalarEmbedding` at the positive size `B.positive i`.
For surjectivity it uses `Subgroup.center_pi` and Mathlib's
`Matrix.GeneralLinearGroup.center_eq_range_scalar` on each block, then chooses
the scalar in every block. `blockScalarCenterEquiv` packages this bijection as a
group isomorphism. The construction also allows the empty block family.

`Classification.HasScalarCharacter.isOpen_ker` proves that an exact scalar
character along a continuous group homomorphism has open kernel when the
representation is smooth and its complex carrier is nonzero. A nonzero vector
has an open stabilizer. The inverse image of this stabilizer lies in the
character kernel, since scalar multiplication on that vector is faithful.
This argument is adapted from Worker 349's private helper
`scalarCharacter_open_kernel` in `TemperedExponentEdgeProof`.

`Classification.HasScalarCharacter.eq_unitaryCentralCharacter` compares a
prescribed character along any central homomorphism with an actual
`UnitaryCentralCharacter`. The two scalar actions agree on a nonzero vector, so
the character values agree. It makes no smoothness assumption.

For the actual topology supplied by `T : F.TopologicalData`,
`T.unitaryCentralCharacterOfBlockScalar` transports a prescribed block-scalar
character `χ` across `blockScalarCenterEquiv`. Its assumptions are smoothness,
exact scalar action, nonzero carrier, and norm one for every value of `χ`.
The full-center inclusion is continuous, so the open-kernel lemma applies to
the transported character directly; continuity of the inverse group
isomorphism is not needed. Its norm-one property and scalar action follow from
those of `χ`. The theorem
`unitaryCentralCharacterOfBlockScalar_character` checks that the result restricts
back to the original `χ`.

Finally, `T.norm_blockScalarCharacter_eq_one_of_isTemperedModCenter` extracts the
actual unitary central-character datum from analytic temperedness and applies
the scalar comparison. It works for every measurable structure and Haar
measure appearing in `IsTemperedModCenter`; it uses no integral estimate,
irreducibility, source representation, or tensor-product presentation.
The field and representation-carrier universes remain independent.

The provenance is internal and algebraic: these are constructions and proved
consequences of the existing center, scalar-action, smoothness, and analytic
temperedness definitions. No additional literature theorem is assumed.
