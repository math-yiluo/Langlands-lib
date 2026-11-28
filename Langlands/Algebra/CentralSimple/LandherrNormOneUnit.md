# Norm-one scalars avoiding the spectrum of an element

Module: `Langlands.Algebra.CentralSimple.LandherrNormOneUnit`.

Let `E/F` be a separable quadratic extension with `CharZero F`, `σ` its conjugation and
`r = skewRoot F E` (module `Langlands.Algebra.CentralSimple.LandherrQuadraticData`).

- `normOneSeq F E k = (k + r) / (k - r)` for `k ∈ ℕ`; the denominators and numerators are
  nonzero (`natCast_add_skewRoot_ne_zero`, `natCast_sub_skewRoot_ne_zero`, since `r ∉ F`),
  `normOneSeq_mul_conj` says `μ σ(μ) = 1` (as `σ(k + r) = k - r`), and
  `normOneSeq_injective` says these elements are pairwise distinct.
- `exists_normOne_isUnit_sub`: for every `z` in a finite-dimensional `E`-algebra `B` there is
  `μ ∈ E` with `μ σ(μ) = 1` and `μ - z` invertible in `B`.

## Proof of `exists_normOne_isUnit_sub`

Left multiplication by `z` has only finitely many eigenvalues
(`Module.End.finite_hasEigenvalue`), while the norm-one elements `normOneSeq F E k` form an
infinite set, so some `μ = normOneSeq F E k` is not an eigenvalue. If left multiplication by
`μ - z` were injective, it would be surjective by finite dimensionality. Taking a preimage of `1`
would give a right inverse, which implies invertibility in the Artinian ring `B`. Thus a nonunit
`μ - z` gives a nonzero `x` with `(μ - z) x = 0`, an eigenvector of left multiplication by `z`
with eigenvalue `μ`.

## Provenance

Elementary: `E` has infinitely many elements of norm one, and an element of a
finite-dimensional algebra has finitely many eigenvalues. It supplies the central unitary
scalar `μ` needed for the cancellation step (module
`Langlands.Algebra.CentralSimple.LandherrCancellation`) in the proof of Landherr's theorem.
