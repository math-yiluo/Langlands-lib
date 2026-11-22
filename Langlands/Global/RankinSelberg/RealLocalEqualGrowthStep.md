# The real equal-rank successor step with strip growth

This module is the real counterpart of the published complex module
`ComplexLocalEqualGrowthStep`. It assembles the canonical-range step of
`RealLocalEqualCanonicalGrowth` into Worker 1050's rank-indexed equal predicate. It also reduces
the target `RealLocalUniformPositiveEqualContinuationStatement` to explicitly named premises.

## Premises (definitions)

The three premises below are open inputs, defined as propositions. They are not proved here.

* `RealUniformCanonicalRangePremise`: for every rank index `r`, nonzero real `a`, parities `p` and
  complex exponents `z` indexed by `Fin (r + 1)`, the uniform Whittaker model
  `realUniformWhittakerModel r (characterList p z) (-a)` is contained in the range of Worker 771's
  canonical Jacquet map `canonicalJacquetMap a p z`. The reverse inclusion is already known: the
  canonical map is a uniform Whittaker intertwiner for the character `-a`
  (`realGodementCanonicalModel`). The canonical map is nonzero at every exponent
  (`realGodementCanonicalNonzero`). This premise plays the role of the complex canonical range
  description in `ComplexJacquetCanonicalRange`, which follows there from
  `ComplexJacquetIdentityProportionality`.
* `RealCanonicalStandardEvaluationPremise`: for all `r, a, p, z`, the canonical map
  `canonicalJacquetMap a p z` has a continuous Whittaker evaluation in the sense of
  `RealStandardCompactBanach.IsWhittakerStandardEvaluation (characterList p z) (-a)`. This is a
  continuous linear functional on the smooth vectors of the compact Banach representation whose
  translates recover the canonical coefficients. The Library's `realSmoothWhittakerEvaluation`
  gives such an evaluation only for irreducible standard modules, under the Casselman–Wallach
  extension premise. At arbitrary exponents the standard module may be reducible, so the premise
  is stated for the canonical maps themselves.
* `RealMatrixCoefficientGrowthPremise t`: for real quotient data `D'` of rank `t + 1`, a nonzero
  real `a`, a parity `e`, a list `fs` of `t + 2` real character data, a standard vector `f` and a
  square Schwartz test `Ψ` with finite-dimensional left orthogonal span,
  `RealMatrixCoefficientNormalizedGrowth` holds. Its lists are `[charData e 0]` and `fs` with
  their duals, with parameter `-a`, scale `√|a|` and sign `1`. This is the matrix input of the
  steps `RealLocalEqualFiniteSquareNormalized` through `RealLocalEqualCanonicalGrowth`. Worker
  823's planned normalized matrix theorem (`RealMatrixPairNormalizedGrowthStatement`) is
  expected to provide it.

## Helper statements

* `exists_characterList_eq`: every list `cs` of real character data of length `n` equals
  `characterList p z` (after mapping to blocks), with `p i` and `z i` the parity and exponent of
  the `i`-th entry. The proof uses `List.ofFn_get` and the Library's `charData_eta`.
* `hasRealPairNormalizedGrowth_neg_neg`: `HasRealPairNormalizedGrowth` with parameter `-(-a)`
  and scale `√|-a|` is the same property as with parameter `a` and scale `√|a|`.

## Statements

`RealLocalEqualGrowthStepStatement t` (proved by `realLocalEqualGrowthStep`) assumes the three
premises, with the matrix premise at rank `t`. It also assumes Worker 1050's adjacent character
predicate `RealLocalAdjacentCharacterGrowthAtRank t`. It concludes Worker 1050's equal
character predicate `RealLocalEqualCharacterGrowthAtRank (t + 1)`. Explicitly: for real character
lists `ds, es` of rank `t + 2`, a nonzero real `a`, quotient data `D` of rank `t + 1`, `W` in the
uniform model of `ds` with character `a`, `W'` in that of `es` with character `-a`, and a
Schwartz function `Φ` on `ℝ^{t+2}`, the equal-rank integral of `(W, W', Φ)` and its dual satisfy
`HasRealPairNormalizedGrowth`. The lists are `ds, es` and their duals, with parameter `-a`,
scale `√|a|` and sign `det(ds, -1)^(t+1)`.

`RealLocalUniformPositiveEqualContinuationPremisesStatement` (proved by
`realLocalUniformPositiveEqualContinuation_of_premises`) states that the target
`RealLocalUniformPositiveEqualContinuationStatement` follows from five inputs:

* the Library premise `RealUniformPrincipalSeriesInclusionStatement`;
* the canonical range premise;
* the canonical evaluation premise;
* the matrix premise at every rank;
* adjacent character growth at every rank.

## Proofs

For the step, write `ds = cs.map character` and `es = fs₀.map character` and use
`exists_characterList_eq` to obtain `ds = characterList P Zs` and `es = characterList P' Zs'`.

* The canonical range premise with parameter `-a` writes `W = canonicalJacquetMap (-a) P Zs F`.
* With parameter `a` it writes `W' = canonicalJacquetMap a P' Zs' F'`.
* The larger map `B = canonicalJacquetMap a P' Zs'` is a uniform intertwiner for the list
  `fs = (charData (P' i) (Zs' i))_i` with character `-a` (`realGodementCanonicalModel`). The
  evaluation premise gives its continuous Whittaker evaluation.
* Worker 1050's adjacent predicate is applied at the parameter `-a`, with the larger list `fs`,
  the tail list `(charData (P (i+1)) (Zs (i+1)))_i`, and the Library quotient data
  `realQuotientMeasureData t`. After `hasRealPairNormalizedGrowth_neg_neg`, this is the
  corank-one input of `realLocalEqualCanonicalGrowth`, in the order and with the sign used
  there.
* The matrix premise at `(D, a, P 0, fs, F')` is the matrix input.

`realLocalEqualCanonicalGrowth` then gives the conclusion for `(W, W')`.

The reduction applies Worker 1050's `realLocalUniformPositiveEqualContinuation_of_characterGrowth`
(from `RealLocalCharacterGrowthInterfaces`). Each positive rank is `t + 1`, and the step
supplies equal character growth there.

## Provenance and scope

This is the induction step of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2,
pp. 54–58: the case `(n, n)` follows from the case `(n, n - 1)` for representations induced from
characters. Jacquet writes the first Whittaker function as a Godement section
`W_{Φ, W₁, μ_n, u_n}` (pp. 54–55), after reducing to `K_n`-finite vectors in §8.1 (pp. 53–54).
For the second Whittaker function he uses a continuous Whittaker functional on the induced
representation, whose uniqueness he invokes on p. 4, to expand its compact averages (p. 57). The Lean statement keeps these two inputs as explicit premises: the canonical
range premise and the evaluation premise. The matrix normalized equation (Jacquet's Proposition
4.4, used on pp. 56–58) is the third premise. The passage from character lists to block lists is
Worker 1050's reduction, which keeps `RealUniformPrincipalSeriesInclusionStatement` as a premise.
The module does not prove any of the five premises. It therefore does not prove
`RealLocalUniformPositiveEqualContinuationStatement` unconditionally.

The pairs `RealLocalCharacterGrowthInterfaces`, `RealLocalGrowthInterfaces`,
`RealLocalEqualRankZeroGrowth` and `RealLocalNormalizedGrowth` are Worker 1050's reviewed modules.
They accompany this candidate unchanged.
