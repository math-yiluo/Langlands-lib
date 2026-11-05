# Separating transcendence bases of geometrically reduced field extensions

Authors: Worker 254.

This module is commutative algebra. Everything lives in the namespace
`Langlands.CommutativeAlgebra.GeometricallyReducedSeparatingBasis`. It imports
only Mathlib.

## Main result

`exists_isTranscendenceBasis_and_isSeparable`. Let `k` and `K` be fields, with
`K` a `k`-algebra that is essentially of finite type
(`[Algebra.EssFiniteType k K]`, so `K / k` is a finitely generated field
extension) and geometrically reduced (`[Algebra.IsGeometricallyReduced k K]`).
Then there is a finite set `s : Finset K` such that

- `IsTranscendenceBasis k ((↑) : s → K)`: `s` is a transcendence basis of
  `K / k`, and
- `Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K`: `K` is
  separable over the subfield `k(s)`.

So `K / k` is separably generated.

## Auxiliary result

`linearIndependent_pow`. Let `k` be a field of prime characteristic `p`
(`[Fact p.Prime]`, `[CharP k p]`), and let `A` be a nontrivial commutative
`k`-algebra with `[Algebra.IsGeometricallyReduced k A]`. If a family
`v : ι → A` indexed by a finite type is `k`-linearly independent, then so is
`fun i => v i ^ p`.

## Proof

`linearIndependent_pow`. Write `k̄ = AlgebraicClosure k`. By
`Algebra.isGeometricallyReduced_field_iff`, `k̄ ⊗[k] A` is reduced. It has
characteristic `p`, because `k̄ → k̄ ⊗[k] A` is injective
(`Algebra.TensorProduct.includeLeft_injective`, using that `k → A` is
injective). Suppose `∑ g j • v j ^ p = 0` with `g j ∈ k`. Choose `b j ∈ k̄` with
`b j ^ p = g j` (`IsAlgClosed.exists_pow_nat_eq`). In characteristic `p`,

`(∑ b j ⊗ v j) ^ p = ∑ b j ^ p ⊗ v j ^ p = 1 ⊗ ∑ g j • v j ^ p = 0`

(`sum_pow_char`). Since `k̄ ⊗[k] A` is reduced, `∑ b j • (1 ⊗ v j) = 0`. The
family `1 ⊗ v j` is `k̄`-linearly independent because `k̄` is flat over `k`
(`Module.Flat.linearIndependent_one_tmul`). So every `b j = 0`, and hence every
`g j = b j ^ p = 0`.

`exists_isTranscendenceBasis_and_isSeparable`. Split on the characteristic of
`k` (`CharP.exists'`).

- Characteristic `0`: `k` is perfect, and Mathlib's
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` applies.
- Characteristic `p > 0`: Mathlib's
  `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`
  (MacLane's criterion, direction "linearly independent `p`-th powers ⇒
  separably generated") needs: for every finite `k`-linearly independent subset
  of `K`, the `p`-th powers stay `k`-linearly independent. That is
  `linearIndependent_pow` with `A = K`.

## Provenance

These are internal helper results for
`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof`. The main
result is the implication "geometrically reduced ⇒ separably generated" for
finitely generated field extensions, which Mathlib's `FieldTheory.SeparablyGenerated`
lists among its target equivalences. Mathlib proves the step from linearly
independent `p`-th powers. The step from geometric reducedness to linearly
independent `p`-th powers (`linearIndependent_pow`) is our own short argument
over `AlgebraicClosure k`.
