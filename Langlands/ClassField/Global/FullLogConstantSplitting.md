# Splitting full logarithmic coordinates

For a number field `E` in an arbitrary universe, this module gives a real
linear equivalence

`fullLogSplit E : (InfinitePlace E → ℝ) ≃ₗ[ℝ] (fullLogHyperplane E × ℝ)`.

The scalar factor measures the constant part of a vector. For a field `F`
in an independent universe with `Algebra F E`, the equivalence intertwines
the arithmetic permutation action with the action on the hyperplane and
the trivial action on `ℝ`. No Galois, cyclicity, or number-field hypothesis
on `F` is required.

## Formulas and proofs

`fullLogConstant E` sends `a : ℝ` to the function with value `a` at every
infinite place. Its definition and evaluation formula require only `Field E`.
For `NumberField E`, `fullLogMean E` is the real linear map

`x ↦ (Fintype.card (InfinitePlace E) : ℝ)⁻¹ * infiniteLogSum E x`.

The finite set of infinite places of a number field is nonempty, so its
cardinality is nonzero in `ℝ`. Summing a constant vector proves
`fullLogMean_constant`. Multiplication by this nonzero reciprocal also
proves `mem_fullLogHyperplane_iff_mean_eq_zero`: the coordinate sum
vanishes exactly when the mean does. `fullLogMean_hyperplane` records this
vanishing for an element of the hyperplane.

`fullLogCentered E` sends `x` to
`x - fullLogConstant E (fullLogMean E x)` in the hyperplane. Its landing
proof applies the mean map and uses `fullLogMean_constant`. It fixes
hyperplane vectors and kills constant vectors, as shown by
`fullLogCentered_hyperplane` and `fullLogCentered_constant`.

The forward map of `fullLogSplit` is
`x ↦ (fullLogCentered E x, fullLogMean E x)`. Its inverse is
`(y, a) ↦ (y : InfinitePlace E → ℝ) + fullLogConstant E a`.
Adding back the subtracted mean proves the left inverse; the vanishing
and identity formulas for the mean and centered maps prove the right
inverse. Both components are real linear. The evaluation lemmas
`fullLogSplit_apply` and `fullLogSplit_symm_apply` expose these formulas.
When there is only one infinite place, the hyperplane is zero and this
still gives the stated equivalence.

`fullLogPermutation_constant` proves that every constant vector is fixed
by arithmetic inverse precomposition; it needs only the field and
algebra assumptions. `fullLogMean_permutation` follows from invariance
of the coordinate sum. Subtraction and the fixed constant vector then
give `fullLogCentered_equivariant`. Together these yield
`fullLogSplit_equivariant`: the two components after applying `g` are the
hyperplane action of `g` on the first component and the unchanged second
component.

## Provenance and scope

Milne, *Class Field Theory*, v4.03 (2020), Chapter VII, proof of
Proposition 3.1, printed p.209 (PDF p.218), uses the decomposition
`V = V0 + ℝ e`, where `V0` is the coordinate-sum-zero subspace and `e`
is the all-ones vector, fixed by the group action. Specializing the
place set to all infinite places gives the decomposition here.
The explicit inverse via the mean, the linear-equivalence packaging,
and the equivariance formulas are internal adapters of this source
construction and the arithmetic action in `FullLogGaloisAction`.

This module constructs the real decomposition. It does not yet construct
the enlarged integral lattice or prove any Herbrand-quotient formula.
