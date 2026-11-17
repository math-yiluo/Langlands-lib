# The adjoint action on actual square-zero kernel tensors

Let `R` be a commutative ring, `G` a smooth affine group scheme over `Spec R`,
`A` an arbitrary `R`-algebra, and `I` an actual ideal of `A` with `I² = 0`.
No flatness assumption is made on `A` or `I`.

`idealLieKernelEquiv` is an additive equivalence

`I ⊗[A] Additive (lieKernel G A) ≃+ Additive (kernel G I)`.

It combines the previously constructed comparison with `I ⊗[R] Lie(G/R)`
with actual smooth affine Lie scalar extension and the canonical cancellation
`I ⊗[A] (A ⊗[R] Lie(G/R)) ≃ I ⊗[R] Lie(G/R)`.
The pure-tensor formula `idealLieKernelEquiv_tmul` identifies `i ⊗ X` with
the actual point obtained by evaluating the dual-number tangent vector `X`
in `i`. Its proof first checks the inverse of the base-Lie comparison by the
universal identity cotangent pairing, then uses tensor induction and the
balancing formula `tangentPoint_smul`.

`idealLieKernelEquiv_adjoint` proves that tensoring the actual adjoint action
of `g ∈ G(A)` with the identity of `I` corresponds exactly to actual point
conjugation by `g` on the reduction kernel. Tensor induction reduces the proof
to the evaluation/conjugation compatibility in `SquareZeroKernelConjugation`;
the additive equivalence and the conjugation automorphism handle sums.

The balancing formula and the ideal cotangent evaluation lemma preceding the
smooth section require only an affine target. This is internal derived
content built from the actual coordinate and Lie comparisons. It does not
replace `I` by a base ideal after arbitrary nonflat base change, extend the
comparison to nonaffine targets, or prove the homomorphism lifting theorem.
