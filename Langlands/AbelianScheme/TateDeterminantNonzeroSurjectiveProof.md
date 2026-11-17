# Proof: an endomorphism with invertible rational Tate map is surjective

This module proves `Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveStatement` as the theorem `Langlands.AbelianScheme.tateDeterminantNonzeroSurjective`. Its helper results are in the namespace `Langlands.AbelianScheme.TateDeterminantNonzeroSurjective`.

## Proof

Let `k` be algebraically closed of characteristic zero, `A` an abelian scheme over `Spec k`, `p` a prime and `α : A ⟶ A` with `det V_p(α) ≠ 0`, where `V_p(α)` is the actual rational `p`-adic Tate map `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α`. Write `T = Over.mk (𝟙 (Spec k))`.

1. **`V_p(α)` is surjective.** `exists_hasRelativeDimension_of_field` gives a relative dimension `g`. `p` is a unit of the global sections because `k` has characteristic zero. So the published `geometricPrimeAdicRank` makes the rational Tate module finite-dimensional. `LinearMap.isUnit_iff_isUnit_det` turns `det V_p(α) ≠ 0` into invertibility of `V_p(α)`.
2. **Lifting torsion sections (`exists_lift`).** Let `s : T ⟶ A.X` with `s ^ (p ^ n) = 1`. View `s` as an element of the level group at `p ^ n`. The published `PrimeAdic.evaluation_surjective_of_pow` lifts it to `x` in the integral Tate module. Its divisibility hypothesis is the published `algClosedPointDivisibility`. Choose `w` with `V_p(α) w = toRational x`. The published `exists_prime_pow_nsmul_mem_integralImage` gives `m` and an integral `w'` with `toRational w' = p ^ m • w`. Applying `V_p(α)` and using the injectivity of `toRational` (published `toRational_injective`) gives `T_p(α) w' = p ^ m • x`. Evaluate at level `n + m`. The section `z` of `w'` at that level satisfies `z ≫ α = p ^ m • (section of x at level n + m)`. By `toSection_evaluation_add` (iterated `evaluation_transition` and `toSection_transition_succ`), this equals the section of `x` at level `n`, which is `s`.
3. **Surjectivity (`surjective_of_rationalMap`).** By step 2, the published torsion locus `Tate.PrimePowerTorsion.locus A p` lies in the image of `hom α`. The morphism `hom α` is proper, by `IsProper.of_comp` and `Over.w`, so its image is closed. The torsion locus is dense: this is the published `Tate.PrimePowerTorsion.dense_locus`, which needs characteristic zero. So the image is everything.

## Provenance

The statement is the contrapositive of the non-isogeny case of Milne's chain in the proof of Proposition 12.9 (*Abelian Varieties*, author revision 2022, p. 23), split off from Milne's Proposition 8.1. The proof is internal. It combines the published Tate-module API, point divisibility and the density of `p`-power torsion. The density theorem's source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Theorem (5.30).
