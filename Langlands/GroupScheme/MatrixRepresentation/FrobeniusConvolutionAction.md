# Actual Frobenius convolution and the original distribution action

Fix an arbitrary field `k : Type u`, an affine group scheme `G` over `k`, its
exponential characteristic `p`, a natural height `r`, and an actual finite matrix
representation `ρ` of `G`. Write `Q` for the original group's actual Frobenius
augmentation quotient `FrobeniusCoordinateModel.quotientAlgebra G p r`.

`DistributionAlgebra` is the full `k`-linear dual of `Q` with Mathlib's
convolution algebra structure, using the inherited quotient bialgebra. The
`WithConv` wrapper distinguishes this multiplication from other multiplications
on linear maps. Explicitly, multiplication contracts the quotient coproduct
against the two functionals and then multiplies their values in `k`; the unit is
the quotient counit. The full dual is allowed even without a finiteness
assumption on `Q`.

`coefficientMatrix` is the matrix of the original representation at the genuine
quotient point. `coefficientMatrix_apply` identifies each entry with the image
of the corresponding original universal matrix coefficient.
`comul_coefficientMatrix` says that its coproduct is the sum of the row-column
pure tensors, and `counit_coefficientMatrix` says that its counit is the identity
matrix. Both follow by reduction of the already proved original coefficient
identities; no new corepresentation is substituted for the original action.

`actionLinear` is the previously constructed `distributionAction` composed
with the linear equivalence forgetting `WithConv`. The lemmas
`actionLinear_one` and `actionLinear_mul` prove that it preserves the unit and
multiplication. For multiplication, contraction of the coefficient coproduct
gives exactly matrix multiplication, and the column-vector matrix action turns
this into composition in the same order. `actionAlgHom` packages these results
as a unital `k`-algebra homomorphism into the endomorphisms of the original
representation. The theorem `range_distributionAction` identifies the entire
linear distribution operator range with the underlying submodule of this
algebra image. This is an image statement, with no injectivity claim.

The earlier universal-quotient orbit-range comparison gives the remaining
conclusions without an ordered-coordinate presentation. The unit proves
`mem_originOrbitSpan`: the original vector belongs to its intrinsic
Frobenius-origin orbit span. Multiplication proves
`distributionAction_mem_originOrbitSpan`: every quotient distribution preserves
that span. `originPoints_mem_originOrbitSpan` translates the same assertion to
scalar contractions of the original action at every intrinsic origin point
over every commutative test algebra in universe `u`, including nonreduced test
algebras. Finally, `originOrbitSpan_le` shows that the span is contained in every
subspace containing the vector and stable under all quotient distributions.
Together these lemmas give its usual cyclic-subspace characterization.

This is an internal derived unit with no external citations. Its provenance is
the actual quotient bialgebra, the published original coefficient identities,
Mathlib's convolution construction, the existing distribution action, and the
universal-quotient orbit-range theorem. No smoothness, reducedness, perfection,
ordered-coordinate
existence, finite-dimensional quotient, or Steinberg representation is assumed.
The unit proves neither independence of the distribution operator images nor a
comparison with an entire induced representation. The general Steinberg
big-cell proposition remains unproved.
