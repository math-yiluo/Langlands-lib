# Admissible smooth-vector recovery

Authors: Workers 386 and 621.

This module proves the published smooth-vector recovery statement.

The theorem `Langlands.admissibleSmoothVectorRecovery` has type
`Langlands.AdmissibleSmoothVectorRecovery.{uG,uV,uH}`. It identifies the
vectors with open stabilizer in a dense form-preserving realization with the
actual image of the original algebraic representation.

## Scope

The group, source carrier and target carrier have independent universes.
The source representation `ρ` is admissible and has an actual invariant
positive Hermitian form `b`. Compact open subgroups are explicitly cofinal
among open subgroups. The target is a complex normed inner-product space
with representation `σ`, and each operator `σ g` is continuous. The actual
intertwiner `j` has dense range and satisfies
`inner ℂ (j v) (j x) = b.inner v x`.

These are precisely the target statement's premises. Completeness, strong
continuity, irreducibility and nonzero carriers are unnecessary. The source
carrier remains algebraic, with no imposed topology or norm.

## Implemented proof

First prove that every target operator preserves the inner product. For fixed
`g`, the equation
`inner ℂ (σ g x) (σ g y) = inner ℂ x y`
defines a closed subset of the product of two target spaces, by continuity
of `σ g` and of the inner product. On pairs `j v, j x`, equivariance and
the exact pullback equation reduce it to `b.invariant`. Mathlib's
`DenseRange.induction_on₂` extends this identity to all pairs of target
vectors.

For a vector `w` fixed by an open subgroup `K`, form the algebraic linear
functional
`ℓ(v) = inner ℂ w (j v)`.
It is linear because the inner product is linear in the second variable.
The dual action is `ℓ ↦ ℓ ∘ ρ(g⁻¹)`. For `k ∈ K`, equivariance rewrites its
value as `inner ℂ w (σ k⁻¹ (j v))`. Apply the established inner-product
invariance to `w` and `σ k⁻¹ (j v)`, then use `σ k w = w` and the
representation inverse law. The result is `ℓ(v)`, so `ℓ` belongs to the
existing smooth dual.

The published `InvariantPositiveForm.toSmoothDual_surjective`, applied
with the stated cofinality and admissibility hypotheses, supplies `v` with
`b.inner v x = ℓ(x)` for every source vector `x`. Pullback now gives
`inner ℂ (j v) (j x) = inner ℂ w (j x)` on the dense image. Mathlib's
`DenseRange.eq_of_inner_left` yields `j v = w`, proving the required
actual preimage.

Conversely, source admissibility includes smoothness. Choose an open
subgroup fixing `v`. Equivariance transports this fixed-vector equation
through `j`, so the same subgroup fixes `j v`.

## Provenance and application boundary

The proof follows Worker 386’s unreviewed shared draft, revision 1 of task
`9302f220-2b3f-4193-9f62-193670c5b934`. Worker 621 prepared this paired
module from that design for checking and independent review.

This is an internal derivation from the stated Library objects and
`Unitary.HermitianDual`, together with Mathlib's continuity and dense-range
inner-product lemmas. It is not a transcription of an external theorem.
The cofinality and admissibility assumptions enter through the existing
Hermitian-dual surjectivity theorem.

The result applies to any realization supplying these actual data. It
constructs no completion, coefficient embedding, irreducibility comparison
or Whittaker functional. Those remain separate inputs to the intrinsic
genericity argument.
