# Stable pair gamma comparison from its three inputs

Author: Worker 389.

This module proves that three statements together imply the stable pair gamma comparison
under highly ramified twists, `ClassField.Global.RelativeWeilGroup.StableTwistPairGammaMatchStatement`
(module `Langlands.Automorphic.StableTwistGammaMatchStatement`). The three statements are
explicit hypotheses of the theorem; this module proves none of them:

- `RankinSelberg.PairGammaTwistExchangeStatement` (`hR1`): a twist by `χ ∘ det` can be moved
  between the two factors of a JPSS pair gamma factor;
- `ArithmeticStableTwistGammaStatement` (`hA`): arithmetic pair gamma factors of Weil–Deligne
  pairs with the same ranks and determinants agree after a twist of large conductor;
- `PrincipalSeriesPairGammaMatchStatement` (`hPS`): the pair gamma match for generic
  constituents of principal series and the matching diagonal Weil–Deligne pairs.

It introduces no definition and no axiom. Like `ClassStability`, it declares three named local
instances (`assemblyTopology`, `assemblyGLTopology`, `assemblyGLTopologicalGroup`) for the
canonical topologies of `K` and `GL_n(K)`.

## Declaration

- `Langlands.Automorphic.StableTwist.stableTwistPairGammaMatch_of hR1 hA hPS`, at universe
  levels `u, uV, uE`: `StableTwistPairGammaMatchStatement.{u, uV, uE}`, with
  `hR1 : PairGammaTwistExchangeStatement.{u, u, u}`,
  `hA : ArithmeticStableTwistGammaStatement.{u, uV, uE}` and
  `hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE}`.

## Implemented proof

Fix the data of the target: `K`, `eC`, `ε`, `hε`, `e` with `IsBaseReciprocity K e eC`, `ψ`,
classes `π`, `π'` of ranks `r + 1`, `t + 1` with generic representatives `A`, `A'` and central
characters `ω`, `ω'`, and pair classes `X`, `Y` with continuous representatives of ranks
`r + 1`, `t + 1` and determinants `ω ∘ e`, `ω' ∘ e`.

1. **Principal-series models.** `exists_generic_principalSeries_object` (module
   `StableTwist.PrincipalSeriesModel`) gives quasi-characters `μ` (resp. `μ'`) with product
   `ω` (resp. `ω'`) and a generic object `A₀` (resp. `A₀'`) that is a subquotient of the
   principal series `i(μ)` (resp. `i(μ')`) and has central character `ω` (resp. `ω'`).
2. **Diagonal models.** `localDiagonal K e μ` (module `StableTwist.DiagonalModel`) is the
   diagonal Weil–Deligne pair with entries `μ_i ∘ e`; `localDiagonal_spec` gives rank `r + 1`,
   zero monodromy, continuity, determinant `(∏ μ_i) ∘ e = ω ∘ e`, and an upper triangular
   basis with diagonal entries `μ_i ∘ e`. The same holds for `μ'`.
3. **Arithmetic stability.** `hA` applied to `(X, [localDiagonal μ])` and
   `(Y, [localDiagonal μ'])`, which have equal ranks and determinants, gives a bound `N₁`.
4. **Representation-side stability.** `A` and `A₀` have the same central character: `A` acts
   centrally by `ω` (`AssemblyDeterminant.centralActsBy_apply`) and `A₀` by step 1; likewise
   `A'`, `A₀'`. `classPairGammaStability hR1` (module `StableTwist.ClassStability`) gives a
   bound `N₂`.
5. **Matching after the twist.** Take `N = max N₁ N₂`. Let `χ` have conductor at least `N` and
   let `πχ` be a twist of `π` by `χ`. Choose a twist `π₀χ` of `[A₀]` by `χ`
   (`exists_isCharacterTwist`); it has a generic representative that is a subquotient of
   `i(μ χ)` (`exists_generic_subquotient_twist`). `hPS` applied to `(π₀χ, [A₀'])` and the
   diagonal pairs of `μ χ` and `μ'` gives the pair gamma match of these four; the twisted
   diagonal class of `μ` is the diagonal class of `μ χ` (`twistClass_localDiagonal`). The match
   supplies the existence of a self-dual measure and, for each self-dual `ν`, a `G` that is a
   class gamma factor of `(π₀χ, [A₀'])` and an arithmetic gamma factor of
   `(twistClass (χ ∘ e) [localDiagonal μ], [localDiagonal μ'])`. By step 4, `G` is a class gamma
   factor of `(πχ, π')`; by step 3, `G` is an arithmetic gamma factor of
   `(twistClass (χ ∘ e) X, Y)`. This is the pair gamma match required by the target.

## Sources and provenance

This is the argument of Henniart, *On the local Langlands conjecture for GL(n): the cyclic
case*, Ann. of Math. 123 (1986), Lemma 4.2 and its proof, printed p.158
(`henniart-1986-cyclic`): both sides of the correspondence are compared with principal
series attached to characters with the same product, using Jacquet–Shalika stability on the
representation side (Jacquet and Shalika, Math. Ann. 271 (1985), Proposition (4.1),
`jacquet-shalika-1985-ramified-factors`) and Deligne–Henniart stability on the arithmetic
side (Deligne and Henniart, Invent. Math. 64 (1981), Theorem 4.6,
`deligne-henniart-1981-variation`). Henniart uses the characters `(ω, 1, …, 1)`; here the
characters are chosen by `exists_generic_principalSeries_object` (unitary part of `ω` in one
entry, a common unramified character in all entries) so that the generic constituent is
available from the Library. The formal organization into three hypotheses is internal.
