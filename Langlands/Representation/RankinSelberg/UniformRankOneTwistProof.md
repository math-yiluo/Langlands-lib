# Level-uniform rank-one stability under highly ramified twists

Module `Langlands.Representation.RankinSelberg.UniformRankOneTwistProof`.

Authors: Worker 1836 and Worker 1807.

The module proves the Library statement
`Langlands.RankinSelberg.UniformRankOneTwistStatement`
([UniformRankOneTwistStatement](UniformRankOneTwistStatement.md)) as the theorem
`Langlands.RankinSelberg.UniformRankOneTwist.uniformRankOneTwist`. Its helper
modules are [UniformRankOneTwistTest](UniformRankOneTwistTest.md) (Worker 1807),
[UniformRankOneTwistLVanishing](UniformRankOneTwistLVanishing.md) and
[UniformRankOneTwistEpsilon](UniformRankOneTwistEpsilon.md).

## Route

Jacquet–Shalika 1985 prove Proposition (2.2) (printed page 320) in §§2.3–2.7
(printed pages 320–323) through the supercuspidal case and multiplicativity.
The implemented proof follows a different route, applied directly to every
irreducible admissible generic `π`. It uses the Godement–Jacquet functional
equation of the twist `σ = π ⊗ χ ∘ det` together with the published JPSS–GJ
rank-one comparisons. Every bound depends only on the principal level `m`.

## Assembly lemmas

* `isGeneric_rankOneCharacter_one`: the trivial character of `GL_1` is
  generic. It is irreducible by
  `Classification.isIrreducible_of_linearEquiv_complex`, and admissible by
  `rankOneCharacter_isOfWhittakerType`.
* `isGeneric_twist`: a quasicharacter twist of a generic representation is
  generic. Irreducibility comes from `isIrreducible_twist_iff`, full Whittaker
  type from `isOfWhittakerType_quasicharacter_twist_iff` and
  `isOfWhittakerType_of_isGeneric`, and the nonzero functional from the
  one-dimensional functional space.
* `twist_apply_of_mem_fixedVectors`: a `K_m`-fixed vector of `π` is an
  eigenvector of `σ(k)`, with eigenvalue `χ(det k)`, for `k` in `K_m'`,
  `m ≤ m'`.
* `twistedModel_package`. Let `π` be generic with a nonzero `K_m`-fixed vector,
  and suppose `max m 1 < a(χ)`. Then there are a nonzero standard functional
  `ℓ` of `σ`, constants `c, a`, and a vector `w` of the coefficient model `ρ` of
  `ℓ`, with the following properties:
  - `ρ` is irreducible and of full Whittaker type;
  - `ρ` carries normalized matrix functional-equation data `(1, 1, c, a)`;
  - `w ≠ 0` is a `χ ∘ det`-eigenvector for `K_(max m 1)`;
  - `L(s, σ × 1) = 1`;
  - `γ(s, σ × 1, ψ) = rationalGammaExpression (residueReflection F) c a 1 1`;
  - `ε(s, σ × 1, ψ) = (c, a)`.

  The data come from the published `genericMatrixFunctionalEquation`. The
  polynomials are `1` by
  [UniformRankOneTwistLVanishing](UniformRankOneTwistLVanishing.md). The
  L-factor comes from `exists_modelMatrixNormalizedGenerator` and uniqueness of
  normalized generators. The gamma factor is the published
  `rankOneMatrixFunctionalEquationComparison`. For the epsilon factor, the
  published generic gamma unit `genericSymmetricGammaFactor` satisfies
  `genericSymmetricGammaFactor_eq_expression` (epsilon times the L-ratio) and
  is unique (`genericSymmetricGammaFactor_eq`). With the L-polynomial equal to
  `1` (`genericSymmetricLPolynomial_eq`), the published cancellation lemma
  `rationalGammaExpression_cancel` compares the two gamma expressions. It
  allows different dual polynomials with constant term `1`
  (`genericSymmetricDualLPolynomial_coeff_zero`), so the dual L-factor need not
  be computed. It yields `genericSymmetricEpsilonData = (c, a)`.
* `model_hasGLCentralCharacter`: if `π` has central character `ω`, the
  coefficient model of `σ` has central character `ω χ^(r+1)`. This uses
  `Matrix.GeneralLinearGroup.det_scalar` and the surjective intertwiner
  `Whittaker.modelMap`.
* `exists_hasGLCentralCharacter`: Schur's lemma for the scalar subgroup. It
  applies the published `exists_centralCharacter_of_isIrreducible` to the range
  of `Matrix.GeneralLinearGroup.scalar`, which is central by
  `Matrix.GeneralLinearGroup.scalar_commute`.
* `uniformRankOneTwist_of_core` assembles both clauses of the target for one
  field, character and measure, with `B = 2 max(m,1) + 1`. Its input `hB` is the
  explicit computation: it determines the exponent `a = (r+1) a(χ)` and the
  constant `c` as a function of `χ` and the central character of the model.
  The first clause takes the L-factor and the epsilon `(c, a)` from the
  package. The second compares two representations with the same central
  character: their models have the same central character `ω χ^(r+1)`, hence
  the same `(c, a)`, hence the same gamma expression.

## The explicit computation and the final theorem

The input `hB` of `uniformRankOneTwist_of_core` is
`twistedMatrixEpsilon` from
[UniformRankOneTwistEpsilon](UniformRankOneTwistEpsilon.md), with the constant
`const χ ω = twistedMatrixEpsilonConstant F ψ ν r χ ω`. Its hypotheses are met as
follows. Smoothness of the model is part of its full Whittaker type. The
eigenvector level is `m' = max m 1`, so `1 ≤ m'`. The conductor bound
`2 max(m,1) ≤ a(χ)` is the bound in `hB`, and `ψ` has conductor exponent `0` by
the hypothesis of the target. `twistedMatrixEpsilon` then gives
`a = (r+1) a(χ)` and `c = twistedMatrixEpsilonConstant F ψ ν r χ ω`.

`uniformRankOneTwist` introduces the field, the character, the self-dual measure,
the rank and the level, and applies `uniformRankOneTwist_of_core` with this
constant. The bound is `B = 2 max(m,1) + 1`, which depends only on `m`. It is used
for both clauses of the target: the L-factor and epsilon clause, and the common
gamma clause for two representations with the same central character.
