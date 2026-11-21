# Right translation orbits of vector-valued coordinate polynomials

Let `A` be a normed ring (in applications, an archimedean matrix algebra) and let `ι : G →* Aˣ` send a monoid `G` into its units. `matrixRightTranslation ι` is the complex representation of `G` on functions `A → V` with values in a complex normed space, given by right translation: `(matrixRightTranslation ι k f)(a) = f(a · ι(k))`.

When `A` is finite dimensional over the reals, the orbit of a vector-valued coordinate polynomial `p` is finite dimensional (`matrixRightTranslation_isFiniteVector`). Its orbit span lies in the span of all right translates `a ↦ p(a · b)` by arbitrary `b` in `A`, which is finite dimensional for coordinate polynomials. Smoothness of `p` extends to every function in the orbit span (`contDiff_of_mem_matrixRightTranslation_orbitSpan`). A left covariance equation `j(p(t · a)) = D(j(p(a)))`, for a linear map `j` into a coefficient space and an operator `D` on it, also extends to the orbit span (`matrixRightTranslation_orbitSpan_covariant`). Both extensions use associativity of multiplication and the linearity of the defining identities.

This is an internal construction of a compact-finite seed family for the archimedean factor in the adelic induction of Langlands, *On the notion of an automorphic representation* (1979), Lemma 1, printed p. 203, Corvallis Part I PDF p. 198.
