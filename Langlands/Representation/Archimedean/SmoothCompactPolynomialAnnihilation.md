# Monic annihilation of compact-finite smooth vectors

Worker 1028, Task 7767. This internal lemma uses the genuine smooth admissibility predicate of [SmoothCompactAdmissibility](SmoothCompactAdmissibility.md). It produces, for each compact-finite smooth vector, the monic polynomial equation needed by the analytic-regularity step of the Harish-Chandra comparison.

`A` is a complete normed real algebra, `R` a representation of `Aˣ` by bounded complex-linear operators, `D` its genuine smooth carrier, and `K` a subgroup of the units. `subgroupRepresentation R K` is the transported genuine action restricted to `K`. All declarations are in `Langlands.Archimedean.DerivativeSmoothVectors`.

`postcompIntertwiners R K Ω hΩ d τ` takes an endomorphism `Ω` of `D` commuting with the action of every element of `K` (hypothesis `hΩ`). It postcomposes the smooth intertwiners from a matrix type `τ` of degree `d` with `Ω`. The commutation keeps postcomposed maps intertwining, so this is an endomorphism of `smoothIntertwiners 𝓘(ℝ, A) R K d τ`. `postcompIntertwiners_apply` records its value.

`exists_monic_aeval_eq_zero_of_isFiniteVector` assumes `A` finite-dimensional, `R` jointly continuous and the genuine smooth action admissible for `K` (`DerivativeSmoothVectors.IsAdmissible`). It shows that every vector `v` with finite-dimensional `K`-orbit span is annihilated by a monic polynomial in `Ω`. The proof:

1. The orbit span `S` of `v` is a finite-dimensional subrepresentation. Its matrices `τ` in the chosen basis are continuous. Joint continuity in the genuine word topology (`continuous_representation_units`) makes the orbits of basis vectors continuous. Coordinate functionals on a finite-dimensional Hausdorff topological vector space are continuous.
2. Admissibility makes the intertwiner space for `τ` finite-dimensional. By Mathlib's Cayley–Hamilton consequence `LinearMap.exists_monic_and_aeval_eq_zero`, some monic `p` satisfies `p(postcompIntertwiners) = 0`.
3. The basis coordinate inverse followed by inclusion of `S` is an intertwiner `T₀`; the matrix identity is `KFiniteDual.equivFun_symm_coordRep`. Evaluation at the coordinate vector of `v` intertwines postcomposition by `Ω` with `Ω`, and hence intertwines `p` evaluated on the two operators. Applying this to `T₀` gives `p(Ω)v = 0`.

No unitarity, irreducibility or compactness hypothesis is used beyond admissibility. The operator `Ω` is arbitrary; its intended use is the transported Cartan square sum, whose commutation with the compact action is proved separately.
