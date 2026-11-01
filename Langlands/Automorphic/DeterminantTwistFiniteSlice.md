# Actual finite slices under full determinant multiplication

Let `F` be an actual number field in an arbitrary universe, and let `χ` be
an actual Hecke character of finite order. For any natural rank and any
full operator realization `S`,
`OperatorRealization.toFiniteRealization_determinantTwist` proves equality
of two actual subspaces of automorphic forms: the finite image of the full
determinant-multiplied realization, and the determinant-multiplied finite
image of the original realization. This is equality of embedded subspaces,
not just equality of representation classes. The preceding
`formInclusion_determinantTwistEquiv` gives the underlying equality of
actual form vectors.

The subspace proof uses the existing image definitions. In one direction,
surjectivity of the full multiplication equivalence writes every vector
in the full multiplied realization as an actual product. Its form image
is the finite multiplication of the original form image. In the other
direction, a vector in the multiplied finite image has an original
full-realization witness, whose full multiplied vector supplies the
required witness.

For positive rank and with the existing compactness hypothesis on the
additive adele quotient, `CuspidalOperatorRealization.FiniteSlice.determinantTwist`
maps any supplied nonzero finite slice of a supplied cuspidal operator
realization into its actual determinant twist. Its subspace is precisely
the existing finite determinant image. The proved equality above and
monotonicity of actual multiplication prove containment in the full
finite image. Injectivity of multiplication preserves nonzeroness.
Cuspidality is inherited from containment in the full cuspidal image,
as in the existing definition of a finite slice.

`determinantTwistEquiv` is the actual continuous complex-linear
multiplication equivalence on the slice. Its evaluation formula is
the positive determinant-character multiplier at the same adelic matrix.
`determinantTwistRepresentationEquiv` compares the existing scalar twist
of the original finite action with the action on this actual image.

Provenance is internal: the construction joins the published full and
finite actual-image multipliers and the existing nonzero finite-slice
definition. It assumes a supplied realization and slice, and proves their
image containment and nonzeroness. It introduces no irreducibility or
tensor-factorization requirement on the slice, no new occurrence or
spectral-existence assertion, and no arithmetic association theorem.
