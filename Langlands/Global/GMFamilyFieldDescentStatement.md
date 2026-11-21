# Arthur descent across a field extension

**Exact target.** `Langlands.GMFamily.FieldExtensionDescentStatement`. J. Arthur, *An introduction to the trace formula* (2005), §17, printed pp. 99–100 (PDF pp. 111–112), Lemma 17.5 and its specialization (17.13), `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`; compare Arthur 1988, *The invariant trace formula. I. Local theory*, §7, printed pp. 355–357 (PDF pp. 33–35), Proposition 7.1, `arthur-1988-invariant-trace-formula-I`.

Let `G` be connected reductive over a characteristic-zero field `k` (in particular a number field), `K/k` a field extension, `M` a rational Levi of `G`, and `M₁` a rational Levi of `G_K` factoring through `M_K`. The Lean hypotheses use actual parabolic homomorphisms and rational Levi inclusions, and the factorization is an equality of morphisms into `G_K`. The supplied split components of `M` and `M₁` satisfy the actual `IsSplitComponent` predicates. Affineness and local finite type of the ambient group are explicit algebraic instances; after base change they follow by pullback.

The conclusion is [HasActualFieldDescent](GMFamilyFieldDescent.md). It chooses the map of split components over `K` and Euclidean coordinates in which the smaller cocharacter space embeds and the induced map on parameters is the actual character base change and restriction. It requires the correct nonzero root restrictions, the fine-center projection compatibility and the specialness condition with weight multiplicities. These comparisons are conclusions, not assumptions about two unrelated arrangements or about an arbitrary Weyl-invariant metric.

For every fine `(G_K, M₁)`-family the induced family is independent of the compatible parabolic chosen for each coarse chamber. The proposition asserts its family condition and the smooth extensions of the supplementary sums. For `ξ ∈ 𝔞_{M₁}^M` regular at the intersections for nonzero coefficients, the asserted identity on those extensions is

```
c_M(λ) = ∑_{L₁ ∈ ℒ(M₁)} d^G_{M₁}(M,L₁) c_{M₁}^{Q₁}(λ),   λ ∈ i𝔞_M*.
```

On the right `λ` is read in the fine dual using the parameter comparison; `Q₁` is the chamber at the shifted intersection. The case `λ = 0` is included. The measures in the coefficients and in `θ` are the Euclidean ones from the same coordinates; see the companion definition for the treatment of extra central directions. The result does not assume that `K/k` is proper or Galois. It covers the proper-field case not covered by the [published same-field target](../LinearAlgebra/GMFamiliesStatement.md). The root comparisons, smoothness and descent identity are stated, not proved.
