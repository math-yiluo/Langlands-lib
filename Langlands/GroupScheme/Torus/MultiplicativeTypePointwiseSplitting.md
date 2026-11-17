# Groups of multiplicative type split on an étale neighbourhood of each point

This module proves the pointwise core of the quasi-isotriviality of groups of multiplicative
type (Conrad, *Reductive group schemes*, Appendix B, Proposition B.3.4). The proof below is
derived and does not follow Conrad's argument, which goes through completions and B.3.2.

## Statements

* `diagonalizableSplitTorusIso S I : D_S(I → ℤ) ≅ 𝔾_m^I` (`splitTorus S I`), for a finite
  type `I` with decidable equality. It is the base change from `Spec ℤ` of the published
  `Diagonalizable.splitIso`, followed by the published `splitTorus.baseChangeIso`.
* `IsMultiplicativeType.exists_etale_diagonalizable` (main theorem): let `H` be of
  multiplicative type over a scheme `S` (`IsMultiplicativeType H`, fppf-locally
  diagonalizable with finitely generated character groups) and let `s : S`. Then there is an
  étale `f : U ⟶ S` with `s` in its image such that `H_U` is diagonalizable
  (`IsDiagonalizable`). There are no further hypotheses on `S`, `H` or the universe.

## Proof of the main theorem

1. **Torus part.** Let `j : T ⟶ H` be the universal subtorus of `H` (published
   `IsMultiplicativeType.exists_universalSubtorus`). It is a relative torus, so it splits
   on an étale cover. Choose a member `p : V ⟶ S` whose image contains `s`, with a point
   `v ↦ s`, and an isomorphism `T_V ≅ 𝔾_m^{I'}`.
2. **Affine chart.** Apply Worker 743's `IsMultiplicativeType.exists_affine_chart`
   (module `MultiplicativeTypeAffineChart`) to `H_V` and `v`. This gives:
   * an open immersion `Spec R ⟶ V` containing `v`, over which `G := H_{Spec R}` is affine
     and of finite presentation;
   * a faithfully flat, finitely presented `R → R'`;
   * an isomorphism `ψ : G_{R'} ≅ D_{R'}(Λ)`.

   Write `Λ ≅ (I → ℤ) × A` with `A` finite (published `exists_freeFiniteEquiv`).
3. **Finite part.** Apply `exists_etale_classifying` (module
   `HomScheme.MultiplicativeTargetClassifying`) to `φ₀ = ψ⁻¹ ∘ ι_A`, where
   `ι_A : D_{R'}(A) → D_{R'}(Λ)` is `finiteInclusionOverScheme` for the projection
   `Λ → A`. This gives:
   * an étale `f : X ⟶ Spec R`;
   * a surjective flat `q : Spec R' ⟶ X` locally of finite presentation, with
     `q ≫ f` equal to `Spec R' ⟶ Spec R`;
   * a homomorphism `σ : D_X(A) → G_X` whose base change along `q` is `φ₀`.
4. **Split criterion.** Over `X`, take the following data:
   * the universal subtorus `τ_X : D_X(I' → ℤ) → G_X`. It is the base change of `j`,
     transported along `T_V ≅ 𝔾_m^{I'}` and `diagonalizableSplitTorusIso`. It stays
     universal by the published `IsUniversalSubtorus.baseChange`/`iso_comp`.
   * the homomorphism `σ`;
   * the isomorphism `(G_X)_{Spec R'} ≅ G_{R'} ≅ D_{R'}(Λ)`.

   Worker 743's `isDiagonalizable_of_split_parts` (module `MultiplicativeTypeSplitCriterion`) then shows
   that `G_X` is diagonalizable; it derives the commutativity of `G_X` itself.
5. **Conclusion.** `U := X`, with `X ⟶ Spec R ⟶ V ⟶ S` étale (étale, open immersion,
   étale). Its image contains `s`: `f` is surjective because `q ≫ f` is, and `Spec R`
   contains a point over `v`. Finally `H_U ≅ (G_X)` by the canonical comparisons of
   iterated base changes (`Descent.pullbackComparison`), so `H_U` is diagonalizable.
