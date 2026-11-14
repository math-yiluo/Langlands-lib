# Pair gamma comparison for principal-series constituents: proof

`principalSeriesPairGammaMatchStatement` proves the published proposition
`Langlands.ClassField.Global.RelativeWeilGroup.PrincipalSeriesPairGammaMatchStatement`
(module `Langlands.Automorphic.PrincipalSeriesGammaMatchStatement`) at three arbitrary
universe levels `u`, `uV`, `uE`. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Route

Both sides are computed as the same double product of Tate gamma factors

`G = ∏_j ∏_i tateRationalGamma K ψ ν (μ_i μ'_j)`

(`Langlands.Automorphic.PrincipalSeriesRankOneGamma`), i.e.
`γ(s, π × π', ψ) = ∏ γ(s, μ_i μ'_j, ψ) = γ(s, X ⊗ Y, ψ)`.

1. Unpack the hypotheses. Take automorphic representatives `A`, `A'` of `π`, `π'`. They
   are generic subquotients of `principalSeries K r μ` and `principalSeries K t μ'`.
   Take Weil–Deligne representatives `B`, `B'` of `X`, `Y`: zero monodromy, continuous,
   with upper triangular bases `b`, `b'` and diagonal characters `μ (σ i) ∘ e`,
   `μ' (σ' j) ∘ e`.
2. The self-dual measure `localSelfDualHaar K ψ` exists
   (`isSelfDual_localSelfDualHaar`).
3. For an arbitrary self-dual measure `ν`, the representation side is
   `isAutomorphicPairGammaFactor_principalSeries`
   (`Langlands.Automorphic.PrincipalSeriesAutomorphicGamma`). This is gamma
   multiplicativity for the principal series together with the component comparison.
4. The arithmetic side is `isArithmeticPairGammaFactor_triangular`
   (`Langlands.Correspondence.TriangularArithmeticGamma`), applied with diagonal
   characters `χ_i = μ (σ i)` and `η_j = μ' (σ' j)`. It gives the arithmetic gamma factor
   `∏_i ∏_j tateRationalGamma K ψ ν (μ (σ i) μ' (σ' j))`.
5. The two products agree. Swap the order of the products (`Finset.prod_comm`), then
   reindex the outer product by `σ'` and the inner one by `σ` (`Equiv.prod_comp`).

## Helper modules

The proof uses four new helper modules, each with its own paired Markdown:

- `Langlands.Weil.Representation.TriangularExactClass`
- `Langlands.Automorphic.PrincipalSeriesRankOneGamma`
- `Langlands.Automorphic.PrincipalSeriesAutomorphicGamma`
- `Langlands.Correspondence.TriangularArithmeticGamma`
