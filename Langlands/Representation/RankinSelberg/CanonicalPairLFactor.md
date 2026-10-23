# Canonical pair L-factors and additive-character scaling

Author: Worker 31.

This internal construction specializes `PairLFactor` to the actual measures of
`CanonicalCharacterChange`. It constructs a rational-function unit from an
explicit proof that a common normalized L-polynomial exists, and proves that
scaling the additive character by a field unit preserves the polynomial
relation, its existence, the selected polynomial, and the factor.

## Parameters and measures

Fix `K : PadicField p`, `Fact p.Prime`, and arbitrary supplied
`T : K.TopologicalData`. The field carrier and the two complex representation
carriers have independent universes `uF`, `uV`, and `uW`. The pair consists of
an algebraic complex representation `π` of `GL_(r+1)(K)` and `σ` of
`GL_(n+1)(K)`, for natural `n` and `r`. Smoothness, admissibility,
irreducibility and Whittaker type are not assumed in this transport API.

Every topology, valuation and local-field instance is taken from this same
`T`. Put `q = T.residueCardinality` and `abv = normalizedAbsoluteValue T`.
The quotient measure is `unipotentQuotientHaar K.Carrier n` with the Borel
structures of the supplied topology on the group, its upper unipotent
subgroup, and the left quotient. The scalar Borel structure and second
countability also come from `T`. The supplied scalar
`ν : AdditiveHaarMeasure K.Carrier` is arbitrary and fixed throughout.
In unequal rank, the existing pair relation uses its actual product measure
`rectangularMeasure ν j (n+1)` on every rectangular block. No self-duality
hypothesis or change of `ν` is involved.

The additive character is `ψ : UnitaryAdditiveCharacter K.Carrier`, and its
scaling parameter is any `a : K.Carrierˣ`. The same representations and
measures are used for `ψ` and `ψ.scale a`.

## Conditional construction

`canonicalPairLFactor T n r ψ ν π σ h` is exactly the published
`pairLFactor h`, specialized to the data above. Its argument `h` is a proof
of `PairLPolynomialExists q ψ abv μ ν π σ`, where `μ` is the actual
quotient measure. It is a unit of `RationalFunctions`, the rational-function
field in the variable `X = q^(-s)`.

The imported constructor chooses the common normalized polynomial `P`, proves
its nonzeroness from `P.coeff 0 = 1`, embeds it in the rational-function
field, and takes its inverse as a unit. `canonicalPairLFactor_eq` expresses
the underlying rational function as `(algebraMap ℂ[X] RationalFunctions P)⁻¹`
for any certified pair L-polynomial `P`, by the published uniqueness theorem.
Thus neither the chosen polynomial nor this specification introduces an
uncertified factor value.

## Character-scaling transport

`isPairLPolynomial_characterChange_canonical` proves an equivalence between
the pair polynomial relations for `ψ` and `ψ.scale a`, with the same `P`.
Its proof follows the exact rank dispatch of `IsPairLPolynomial`:

- If `n < r`, it retains the universal quantifiers over every `j`, `k` and
  equation `r = n + (j + k + 1)`. Substitution of that equation identifies the
  transported block with the defining unequal-rank zeta family. The proof then
  uses `isUnequalRankLPolynomial_characterChange_canonical` for that block.
- If `r = n`, it substitutes the rank equation and applies
  `isEqualRankLPolynomial_characterChange_canonical` after unfolding the
  equal-rank branch.
- If `r < n`, both relations are false by the published pair convention.
  The equivalence follows from these two impossibility statements; it does not
  introduce an exchange convention for the representations.

In particular, `n=0` includes smaller rank one, and every permissible `j=0`
block is retained. No positive-dimension restriction is added. The imported
canonical character-change results already establish the quotient and product
measure laws, determinant normalization and required finiteness. This module
exposes no extra measure-scaling or finiteness hypothesis.

`pairLPolynomialExists_characterChange_canonical` transports existence in both
directions by applying the polynomial equivalence under the existential
quantifier. It does not establish existence for either character independently.

`pairLPolynomial_characterChange_canonical` accepts arbitrary existence proofs
`h` and `h'` for the two characters. The chosen polynomial for the scaled
character satisfies the original relation by the reverse implication above;
`pairLPolynomial_eq` then identifies it with the originally chosen polynomial.

Finally, `canonicalPairLFactor_characterChange` proves equality of the actual
rational-function units for these arbitrary witnesses. It applies `Units.ext`,
unfolds the canonical constructors to `pairLFactor`, rewrites both underlying
values using `coe_pairLFactor`, and uses the chosen-polynomial equality.

## Provenance and scope

This is an internal consumer of the published `PairLFactor` and
`CanonicalCharacterChange` Lean/Markdown pairs. The former supplies the
common-generator relation, normalized polynomial choice, uniqueness and unit
construction. The latter supplies character-scaling equivalence for each
actual equal- and unequal-rank family. The only new arguments are the rank
case split, transport of quantifiers, and applications of uniqueness and unit
extensionality. No separate external-source assertion is made here.

The result is conditional on common normalized polynomial existence and
covers character changes specifically of the form `ψ.scale a`. It does not
prove analytic continuation, common-generator existence, or that any two
nontrivial characters are related by such a scaling. It gives no functional
equation, epsilon or gamma formula, conductor formula, nongeneric
classification theorem, or completion of the broad local-factor task.
