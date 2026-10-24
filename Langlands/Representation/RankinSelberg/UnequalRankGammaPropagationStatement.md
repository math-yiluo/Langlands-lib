# Same-multiplier propagation of the unequal-rank gamma equation

Worker 331 authored this statement. The field, measure and representation
scope and the private valuative-topology helper are adapted from Worker 11's
published `FunctionalEquationStatement`. Worker 12 supplied the shared-cutoff
interface plan described below.

`Langlands.RankinSelberg.UnequalRankGammaPropagationStatement.{uF,uV,uW}
F T n r` is a proposition definition, not a proved theorem. It isolates the
block-zero reduction of JPSS §2.8, printed p.395, in the Library's rational
gamma-equation language. The internal packaging is derived from the source;
JPSS does not name this predicate. No existence of a gamma factor or proof of
propagation is supplied by this module.

## Scope and quantifiers

The parameters are any prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural numbers `n,r`. The proposition has exactly
the data hypotheses of `UnequalRankFunctionalEquationStatement F T n r`:

- `hnr : n < r`, a unitary additive character `ψ`, and a right-invariance
  instance for `unipotentHaar F.Carrier n`;
- every quotient measure `μ` compatible with the actual general-linear and
  unipotent Haar measures;
- every supplied scalar additive Haar measure `ν` satisfying `IsSelfDual ψ ν`;
- independent complex representation carriers in universes `uV` and `uW`;
- actual representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)`, of
  Whittaker type for `standardCharacter ψ r` and `inverseStandardCharacter ψ n`;
- every specified pair of nonzero functionals `ℓ,ℓ'` for those characters.

The proposition uses `T.residueCardinality` for `q` and
`normalizedAbsoluteValue T` for the absolute value. It installs the topology
supplied by `T` and the same Borel, uniform and nonarchimedean structures as
the existing functional-equation statement. The private helper derives the
nonarchimedean additive structure from the valuative topology by Mathlib's
basis of open submodules; it adds no assumption.

For each such set of data, **every given** `G : RationalFunctions` satisfies
the implication from the block-zero clauses below to
`UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G`.
There is no choice of a new multiplier in the conclusion, no block-dependent
multiplier, and no hypothesis `G ≠ 0`. Whittaker type is not strengthened to
irreducibility. There are no additional assumptions of rationality, common
generators, gamma or epsilon existence, a central character on either
representation, bilinear uniqueness, or an abstract comparison law.

## Literal block-zero hypothesis

Write `k₀ = r - n - 1`. The rank inequality proves
`r = n + (0 + k₀ + 1)`; the Lean arithmetic proofs supply only this equality.
The antecedent is written directly using the published `GammaFactor`
interfaces. It is exactly the restriction of the existing full equation to
`j = 0`, `k = k₀`:

1. There is `ζ : ℂˣ` with `HasModelMinusOneScalar σ ℓ' ζ`.
2. There is a nonzero rational function in
   `unequalRankValuesAt 0 k₀ hr q ψ abv μ
   (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ'`.
3. For every `f` and `f'` in the actual coefficient models of `(π,ℓ)` and
   `(σ,ℓ')`, there are rational functions `R,Rdual` that are
   `HasRationalContinuation` values of the actual original and transformed
   integrals, and satisfy `GammaFunctionalEquation q ζ r G R Rdual`.

The existential `ζ` precedes all vectors. The nonzero-value clause is a
separate existence clause: individual vectors, including the zero vectors,
may have zero continuations. The continuations retain the Library meaning
of a real bound beyond which the denominator is nonzero at every spectral
point and the rational evaluation equals the actual integral.

The original integral is `unequalRankIntegralAt 0 k₀ hr`. The dual integral
is precisely `dualUnequalRankModelIntegralAt hnr 0 k₀ hr`, whose definition
uses block `k₀`, the inverse character `ψ.scale (-1)`, and the **same** `ν`
in `rectangularMeasure ν k₀ (n + 1)`. Its first function is the right
translate by `blockWeylAt n r hnr` of `firstDualFunction ψ r f.val`; its
second is `secondDualFunction ψ n f'.val`. Thus it retains the long-Weyl
inverse-transpose transforms and the actual block Weyl representative
`diag(I_(n+1),w_(r-n))`. No abstract family replaces these integrals.

Writing `X_s = spectralPoint q s`, the gamma relation says

`Rdual(X_(1-s)) = ζ^r * (G(X_s) * R(X_s))`

whenever the canonical denominators of `R` at `X_s`, `Rdual` at `X_(1-s)`
and `G` at `X_s` are all nonzero. This is the existing
`GammaFunctionalEquation`, including all three denominator conditions and
the reflected argument `1-s`. The exponent is `r`, since the larger group
has rank `r+1`.

## Full conclusion

The conclusion is the unchanged `UnequalRankGammaEquation`, which chooses
one model minus-one scalar before all blocks. For every `j,k` and equality
`r = n + (j + k + 1)`, it requires a nonzero original rational value at block
`j` and the continuation/equation clauses for every coefficient-vector pair,
with complementary dual block `k`. The same supplied `G`, `μ`, `ν`, models,
character and absolute value occur throughout. Although the implication's
conclusion existentially packages its scalar anew, the existing
`HasModelMinusOneScalar.unique` and `ℓ'.val ≠ 0` force it to equal the scalar
from the antecedent.

The adjacent-rank case `r = n+1` is included: its only block is `(0,0)`.
The case `n = 0` includes a rank-one second member.

## Source correspondence and future proof dependency

JPSS Theorem 2.7, pp.390–391, has Whittaker-type scope. Its unequal-rank
formula (2), p.391, uses complementary blocks, the right-translated dual
Whittaker function and sign `ω_(π')(-1)^(r_source-1)`. The source ranks
`r_source,t_source` are Lean `r+1,n+1`, so that sign exponent becomes `r`.
Theorem 2.7(ii) gives generators independent of the block. Consequently
passing between its normalized epsilon formula and a rational gamma
multiplier preserves independence of the block. This explains the derived
gamma formulation without importing an analytic or common-generator
statement as an extra hypothesis.

JPSS §2.8, p.395, says that it suffices to establish block zero and that an
equation at one block implies all the others with the same proportionality
constant. It identifies JPS1979 Theorem 4.5 as the rank-one-test case and
says the general proof replaces JPS1979 Lemma 4.1.5 by the Fourier cutoff
lemma on JPSS pp.394–395. In JPS1979 the induction step in the proof of
Theorem 4.5, pp.197–198, smears a Whittaker vector by right translates,
transfers a Schwartz cutoff to the complementary integral by Fourier
transformation, and chooses the cutoff using support and smoothness. The
multiplier remains fixed in the passage from `j` to `j+1`.

A future proof must implement that root/Fourier transfer for the actual
coefficient models and the supplied measures, together with the rational
continuation and nonzero-value obligations of the conclusion. The shared
cutoff interface planned with the adjacent-span work is a Fourier-weighted
right-translation construction in the same representation: its row-integrated
coefficient equals the original coefficient with a Schwartz cutoff in that
row. It must retain the topology and measure normalization; a version stated
for a differently normalized Haar measure needs explicit nonzero scaling
transport. It must not assume a common generator or the functional equation.
The adjacent-span and functional-equation consumers should share this helper.
This is an unimplemented proof-interface plan, not an additional Lean
hypothesis or an already proved cutoff lemma. Compact rectangular support
and finite Schwartz expansion are separate prerequisites. This module proves
neither the cutoff lemma nor gamma existence, and does not perform epsilon
normalization.

## Originals

- `jpss-1983-rankin-selberg`: Jacquet, Piatetski-Shapiro and Shalika,
  *Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464;
  Theorem 2.7 pp.390–391, Fourier cutoff lemma pp.394–395, and §2.8 p.395.
  Retained original: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
  SHA256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- `jps-1979-gl3-i`: the same authors, *Automorphic Forms on GL(3) I*,
  Ann. of Math. (2) 109 (1979), 169–212; Theorem 4.5 p.194 and its induction
  step pp.197–198. This is the antecedent explicitly cited by JPSS §2.8,
  not an independent claim here of a formal proof for all test ranks.
  Retained original: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
  SHA256: `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
