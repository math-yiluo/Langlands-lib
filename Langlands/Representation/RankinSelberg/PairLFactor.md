# The L-factor of a pair

Worker 31 defines the L-polynomial and the L-factor `L(s, π × σ)` of a pair
`π` on `GL_(r+1)(F)`, `σ` on `GL_(n+1)(F)` for every pair of ranks with
`n ≤ r`, one relation covering equal and unequal rank. The source is Theorem
2.7(ii) of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), printed pages 390–391, in the setting of §2.1, printed
pages 385–386. Both were read from the original scan. The source is registered
as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The module builds on the published `LocalFactor`, which treats one block
`(j, k)` at a time. Its own `AnalyticBridge` and `TwistInvariance`, submitted
with it, are imported. Nothing analytic is proved. The L-factor is built only
from a proof that its L-polynomial exists, and that existence is derived from
Worker 11's unproved analytic statements.

## Whittaker functions of quotients

JPSS formula (3) on page 386 defines `W(π; ψ)` as the functions
`g ↦ λ(π(g)v)`. The source notes that the representation on this space is a
quotient of `π`. `exists_coefficientMap_eq_of_surjective` proves the
underlying fact for any group, subgroup and character. Along a surjective
intertwining map `f : ρ → ρ₂`, every coefficient `g ↦ ℓ₂(ρ₂(g)v₂)` of `ρ₂` is
a coefficient of `ρ`. The functional is `ℓ₂ ∘ f` and the vector is any
preimage of `v₂`.

Hence `whittakerSet_subset_of_surjective` and
`inverseWhittakerSet_subset_of_surjective`: the Whittaker functions of a
quotient (the published union over all functionals in `LocalFactor`) lie among
those of the source. `whittakerSet_eq_of_equiv` and
`inverseWhittakerSet_eq_of_equiv` give equality for equivalent
representations.

The zeta values follow. `equalRankZetaValues_subset_of_surjective` uses the
published monotonicity `equalRankValuesOf_mono`. If the two members of a pair
are quotients of the members of another pair, the zeta values of the first
pair are zeta values of the second. `equalRankZetaValues_eq_of_equiv` gives
equality for equivalent pairs. `unequalRankZetaValues_subset_of_surjective` and
`unequalRankZetaValues_eq_of_equiv` do the same for a fixed block `(j, k)`
and any measure `ν` on the `j × (n + 1)` matrices.

## Blocks at a fixed large rank

The published `unequalRankZetaValues` takes `π` on `GL_(n + (j + k + 1) + 1)`.
So its rank depends on the block. To quantify over all blocks of one fixed
pair, `unequalRankZetaValuesAt j k hr` takes `π` on `GL_(r+1)` and a proof
`hr : r = n + (j + k + 1)`. It substitutes `r` and applies
`unequalRankZetaValues`, so the equation transports only types.

- `unequalRankZetaValuesAt_rfl`: at `hr = rfl` it is the published set,
  definitionally.
- `unequalRankZetaValuesAt_twist`: it is unchanged under the twists
  `π ⊗ (χ ∘ det)` and `σ ⊗ (χ⁻¹ ∘ det)`. This is `TwistInvariance`'s
  `unequalRankZetaValues_twist`.
- `unequalRankZetaValuesAt_eq_of_equiv`: it is unchanged under
  equivalences.

It is the intrinsic counterpart of Worker 11's per-functional
`unequalRankValuesAt` in `AnalyticStatement`.

## The relation

`IsPairLPolynomial q ψ abv μ ν π σ P` has the following parameters:

- `q`: the base of `X = q^(-s)`;
- `ψ`: the additive character;
- `abv`: the absolute value;
- `μ`: a measure on the published left-unipotent quotient of `GL_(n+1)(F)`;
- `ν`: an additive Haar measure on `F`, Worker 20's `AdditiveHaarMeasure`.

It says the following.

- **`n < r`.** For every `j, k` and every proof of `r = n + (j + k + 1)`, `P`
  is the normalized generator (`IsNormalizedGenerator` of `RationalZeta`) of
  `unequalRankZetaValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
  π σ`. Here `rectangularMeasure` is the published product of `ν` over the
  `j × (n + 1)` entries.
- **`r = n`.** `P` is the published equal-rank L-polynomial
  `IsEqualRankLPolynomial q ψ abv μ π σ P`. The rank equation transports `π`.
- **`r < n`.** The relation is false.

So `ν` enters only in unequal rank, and `μ` is a fixed parameter. JPSS
Theorem 2.7(ii) says that for `t ≤ r − 1` there is a factor
`L(s, π × π') = P(q^(-s))^(-1)`, `P(0) = 1`, independent of `j`, that generates
the span of the integrals `Ψ(s, W, W'; j)`. The `n < r` case asks exactly that
one `P` work for every `j` (JPSS rank `t = n + 1`, block index
`j + k = r − n − 1`). The case `r = n` is the equal-rank part of the theorem.

JPSS treat only `t ≤ r`. As in Worker 11's published `IsPairEpsilonFactor`,
whose dispatch is mirrored here, the case `r < n` is false rather than defined
by exchanging the two representations. No exchange convention is formalized.
`not_isPairLPolynomial_of_lt` records this case.

`PairLPolynomialExists` is the existence of such a `P`.
`isPairLPolynomial_of_lt` and `isPairLPolynomial_self` unfold the two nonempty
cases. `IsPairLPolynomial.isUnequalRankLPolynomial` specializes to the
published `IsUnequalRankLPolynomial` of one block when `π` is on
`GL_(n + (j + k + 1) + 1)`.

The relation has the following basic properties.

- `IsPairLPolynomial.unique`: two L-polynomials are equal. In unequal rank the
  block `j = 0`, `k = r − n − 1` alone suffices. No hypothesis on `q` is
  needed, since normalized generators of a set are unique by
  `IsNormalizedGenerator.unique`.
- `IsPairLPolynomial.coeff_zero`: `P(0) = 1`.
- `IsPairLPolynomial.ne_zero`: `P ≠ 0`.

## The factor

`pairLPolynomial h` chooses the polynomial from a proof
`h : PairLPolynomialExists …`. `pairLPolynomial_spec` and `pairLPolynomial_eq`
show that it is the unique L-polynomial.

`pairLFactor h` is the unit `1 / P` of the published `RationalFunctions` (the
rational functions in `X = q^(-s)`), with `P` that polynomial. Its value is
`L(s, π × σ) = 1 / P(q^(-s))`. `coe_pairLFactor` and `pairLFactor_eq` express
it through the chosen and through any L-polynomial.

The factor agrees with `LocalFactor`'s factors in each case:

- `pairLPolynomialExists_self_iff` and `pairLFactor_self`: in equal rank,
  existence is `NormalizedGeneratorExists` of `equalRankZetaValues`, and the
  factor is `equalRankLFactor`.
- `PairLPolynomialExists.unequalRank` and `pairLFactor_eq_unequalRankLFactor`:
  in unequal rank every block has a normalized generator, and the factor is the
  `unequalRankLFactor` of every block.

This factor is unrelated to the Galois-side
`Langlands.LocalFactor.WeilDeligne.pairLFactor`, which lives in another
namespace.

## Invariance

- `isPairLPolynomial_congr_equiv`: equivalent pairs have the same
  L-polynomials.
- `isPairLPolynomial_twist`, `pairLPolynomialExists_twist_iff` and
  `pairLFactor_twist`: the pair `(π ⊗ (χ ∘ det), σ ⊗ (χ⁻¹ ∘ det))`, with the
  published twist of Worker 4, has the same L-polynomial and factor as
  `(π, σ)`. They rest on `TwistInvariance`.
- `isPairLPolynomial_smul_measure`: replacing `μ` by `c • μ` with
  `0 < c < ∞` does not change the relation. It assumes `ν` σ-finite and
  uses `LocalFactor`'s measure-scaling lemmas. Changing `ν` itself is not
  treated.

## The dual pair

JPSS formula (4) on page 386 maps `W ∈ W(π; ψ)` to
`W̃(g) = W(w_r g^ι)`, `g^ι = (gᵀ)⁻¹`, an element of `W(π^ι; ψ̄)`. Here `π^ι` is
`π` composed with `g ↦ g^ι`. Theorem 2.7(ii) states the same for the pair
`(π^ι, π'^ι)`. Its functional equation (iii) relates the integrals of that
pair to those of `(π, π')`.

`IsDualPairLPolynomial q ψ abv μ ν π σ P` is `IsPairLPolynomial` for the
published `inverseTransposePullback π` and `inverseTransposePullback σ` of
`Whittaker/DualTransform`. The additive character is `ψ.scale (-1)`. It is
`ψ⁻¹`, which equals `ψ̄` for the unitary `ψ`, and it comes from the published
`CharacterTransport`. The following are defined from it:

- `DualPairLPolynomialExists`: existence of such a `P`.
- `dualPairLFactor`: the factor `L(s, π^ι × σ^ι)`.
- `dualPairLFactor_eq`: its value through any dual L-polynomial.

`isDualPairLPolynomial_self` and `IsDualPairLPolynomial.dualUnequalRank` show
that this is the normalized generator of `LocalFactor`'s
`dualEqualRankZetaValues`, and of `dualUnequalRankZetaValues` of every block.

JPSS note on page 386 that for irreducible `π`, `π^ι` is equivalent to the
contragredient `π̃` (Gelfand–Kazhdan). That identification is not formalized.
The dual pair here is the inverse-transpose pullback, not the contragredient.

## Existence from the p-adic statements

Worker 11's p-adic statements in `AnalyticStatement` are hypotheses here, not
proved. In both theorems, `F` is a p-adic field with topological data `T`, and
`q = T.residueCardinality`, `abv = normalizedAbsoluteValue T`.
The theorems quantify over every additive character `ψ` and every quotient
measure `μ` compatible (published `IsCompatible`) with `generalLinearHaar` and
a right-invariant `unipotentHaar`. They also quantify over every additive Haar
measure `ν`, and over every `π` and `σ` of Whittaker type (`IsOfWhittakerType`)
for the standard and the inverse standard character.

- `EqualRankAnalyticStatement.pairLPolynomialExists`: the equal-rank statement
  for `n` gives `PairLPolynomialExists` in equal rank. It uses
  `AnalyticBridge`'s `EqualRankAnalyticStatement.normalizedGeneratorExists`.
- `UnequalRankCommonGeneratorStatement.pairLPolynomialExists` assumes `n < r`,
  the common-generator statement for `n, r`, and
  `UnequalRankAnalyticStatement` for every block with `r = n + (j + k + 1)`.
  From these it derives `PairLPolynomialExists`. Nonzero functionals come from
  `IsOfWhittakerType.exists_ne_zero`. The common generator of Worker 11's
  per-functional block values is then the common generator of the intrinsic
  block zeta values. That step uses
  `UnequalRankAnalyticConclusion.zetaValues_eq` of `AnalyticBridge`, block by
  block.

The proofs reintroduce the topology `T.topology` and the Borel σ-algebras on
`F` and on the quotient as local instances, as in `AnalyticBridge`.

## Imports and provenance

The module imports `AnalyticBridge` and `TwistInvariance`. Through them it uses
the published `LocalFactor`, `QuotientIntegrals`, `Measures`, `RationalZeta`,
`AnalyticStatement`, `Whittaker/Twist`, `Whittaker/DualTransform` and
`HarmonicAnalysis/CharacterTransport`.

The relation is the formal reading of Theorem 2.7(ii). The quotient, twist,
equivalence and measure-scaling results are elementary derived results. The
source does not state them as numbered results, apart from the quotient remark
on page 386.
