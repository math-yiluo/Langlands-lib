# The real equal-rank normalized equation on the canonical range

This module extends the generator trace of `RealLocalEqualGeneratorTrace` from the
compact column generators to every coefficient in the canonical range. These are the
coefficients `canonicalJacquetMap (-a) P Zs F` of the character list `characterList P Zs`, for
real characters with arbitrary complex inducing exponents `Zs : Fin (t + 2) → ℂ` and parities
`P`. The argument is the real counterpart of the span step in the
complex module `ComplexLocalEqualGrowthStep`.

## Definition

`equalGrowthSubmodule t D' b V φ xs ys xsd ysd bb c hc sign` is the set of coefficients `W` of
`GL_{t+2}(ℝ)` with two properties:

* for `Re s` beyond some `σ`, the integrands of the real equal-rank integral `Ψ(s; W, V, φ)` and
  of the dual integral `Ψ(s; W~, V~, φ̂_b)` are integrable for the quotient measure of `D'`. Here
  `~` is the Weyl inverse-transpose dual and `φ̂_b = realFourierTransform b φ`;
* the two integrals satisfy `HasRealPairNormalizedGrowth` (module `RealLocalNormalizedGrowth`) with the given lists,
  `ε`-data and sign.

This set is a complex subspace. On a common half-plane the integrals are additive and
homogeneous in `W`, because the integrands are linear in `W` and the dual is linear. The
normalized property is closed under sums, scalar multiples and half-plane agreement
(`HasRealPairNormalizedGrowth.add`, `const_mul`, `congr`).

## Statement

`RealLocalEqualCanonicalGrowthStatement t` fixes:

* real quotient data `D` and `D'` of ranks `t` and `t + 1`, and a nonzero real `a`;
* parities `P` and exponents `Zs` indexed by `Fin (t + 2)`, and a vector `F` of the standard
  `K`-finite module of `characterList P Zs`;
* a real character list `fs` of length `t + 2`, a uniform Whittaker map `B` for `fs` with
  character `-a` that has a continuous Whittaker evaluation, and a standard vector `f`;
* a Schwartz function `φ` on `ℝ^{t+2}`.

Let `cs = (charData (P (i+1)) (Zs (i+1)))_{i < t+1}` be the tail character list. It assumes:

1. for every `U` in the uniform model of `cs` with character `a` and every `V` in the uniform
   model of `fs` with character `-a`, the corank-one integral of `(V, U)` and its dual satisfy
   the normalized equation in the adjacent form (lists `fs, cs` and duals, parameter
   `a`, scale `√|a|`, sign `det(fs, -1)^(t+1) det(cs, -1)`);
2. `RealMatrixCoefficientNormalizedGrowth t D' a (P 0) fs f Ψ` for every square Schwartz test
   `Ψ` with finite-dimensional left orthogonal span, with lists `[charData (P 0) 0]` and `fs`
   and their duals, parameter `-a`, scale `√|a|` and sign `1`. This is the matrix normalized
   equation for the leading sign character `charData (P 0) 0` at exponent zero.

It concludes that, for `W = canonicalJacquetMap (-a) P Zs F` (which has character `a`), the real
equal-rank integral of `(W, B f, φ)` and its dual satisfy `HasRealPairNormalizedGrowth` with:

* lists `characterList P Zs` and `fs`, and their duals;
* parameter `-a` and scale `√|a|`;
* sign `det(characterList P Zs, -1)^(t+1)`.

This is the form of the equal character predicate `RealLocalEqualCharacterGrowthAtRank` at rank `t + 1`.

## Proof

`canonicalJacquetMap_reflectedPair_mem_span` (module `RealGodementCanonicalModel`) puts the pair `(W, W~)` in the span of
`compactReflectedColumnGenerators D (-a) cs (P 0) (Zs 0)`. These are pairs whose first member is
`godementLeadingFamily D (-a) Φ U (P 0) · (Zs 0)`, where `Φ` is a compact full-row-rank test and
`U` lies in the uniform model of `cs` with character `a`. It therefore suffices that the first
member of each generator lies in `equalGrowthSubmodule`. The span then lies in the preimage of
this subspace under the first projection, and the first member of `(W, W~)` is `W`.

For a generator:

* integrability on a half-plane comes from `realLocalEqualGeneratorFamily` (from
  `RealLocalEqualGeneratorFamily`), on a disk containing `Zs 0`;
* the normalized equation is `realLocalEqualGeneratorTrace` (from `RealLocalEqualGeneratorTrace`)
  at `z = Zs 0`, whose list `charData (P 0) (Zs 0) :: cs` is `characterList P Zs` (`List.ofFn_succ`).

## Provenance and scope

This follows the route of Jacquet, *Archimedean Rankin–Selberg integrals* (2009):

* Proposition 7.1(v), p. 43: at fixed complex inducing exponents, every vector of the induced
  representation is a finite sum of Godement sections whose test `Φ` has compact support in the
  full-row-rank matrices;
* §7.2, p. 47: the Whittaker functional applied to these sections;
* §8.1, pp. 53–54: the continuity reduction to `K_n`-finite and standard data;
* §8.2, pp. 54–58: the calculation for the generator data.

The Lean proof implements the spanning step internally, through the span theorem
`canonicalJacquetMap_reflectedPair_mem_span`, its first projection and linearity of the
integrals. This follows the complex module `ComplexLocalEqualGrowthStep`. The statement covers only the canonical range
and real character lists. Equality of a given uniform coefficient model with the canonical range
is a separate open input. The other inputs remain explicit: the continuous Whittaker
evaluation of `B`, the corank-one equation, and the matrix equation. The statement does not prove
`RealLocalUniformPositiveEqualContinuationStatement`.
