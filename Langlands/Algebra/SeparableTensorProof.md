# Proof of the finite separable tensor decomposition

`Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement` proves
`Langlands.Algebra.SeparableTensor.EmbeddingEvaluationStatement` in all three
universe parameters, with no hypotheses beyond those of the statement. It uses
linear independence of field embeddings, rather than a Chinese remainder
theorem presentation of the primitive element construction.

Fix fields `k`, `K` and `Ω` as in the statement, and write `E` for the finite
set of `k`-algebra maps `K → Ω`. The proof has four steps.

1. **Independent functionals.** Mathlib's `linearIndependent_algHom_toLinearMap`
   (Dedekind's independence of characters) gives linear independence over `Ω` of
   the members of `E`, viewed as `k`-linear maps `K → Ω`. The `Ω`-linear
   equivalence `LinearMap.liftBaseChangeEquiv Ω`, from `k`-linear maps `K → Ω`
   to `Ω`-linear maps `Ω ⊗[k] K → Ω`, carries this to an `Ω`-linearly
   independent family `F` in the `Ω`-linear dual of `Ω ⊗[k] K`
   (`LinearIndependent.map'`). By definition (recorded as
   `embeddingEvaluation_linearMap`), `F σ` is the `σ` coordinate of
   `embeddingEvaluation k K Ω`.
2. **Counting.** `AlgHom.card_of_splits`, which uses finite dimensionality,
   separability and the splitting hypothesis, gives `#E = finrank k K`. The
   dual of `Ω ⊗[k] K` has the same `Ω`-dimension, by
   `Subspace.dual_finrank_eq` and `Module.finrank_baseChange`. Hence `F` spans
   the whole dual (`LinearIndependent.span_eq_top_of_card_eq_finrank'`).
3. **Injectivity.** Suppose the evaluation map sends `x` to zero. Then every
   `F σ` vanishes on `x`. The double-dual image of `x` is a linear functional on
   the dual that vanishes on the spanning family `F`, so it is zero
   (`LinearMap.ext_on_range`). By `Module.eval_apply_eq_zero_iff`, `x` is zero.
4. **Surjectivity.** `Ω ⊗[k] K` has `Ω`-dimension `finrank k K`, and the
   function space `E → Ω` has dimension `#E`
   (`Module.finrank_fintype_fun_eq_card`). These are equal by step 2. An
   injective linear map between spaces of equal finite dimension is surjective
   (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`). This gives
   bijectivity of the underlying map, which is the asserted bijectivity of
   `embeddingEvaluation k K Ω`.

The mathematical target and its source, Milne, *Algebraic Groups* (2017), 2.61,
are described in the paired statement Markdown. The route here is a derived
linear algebra proof of its finite separable field specialization. It does
not add hypotheses to that statement. Worker 207 wrote the original draft of
this proof.
