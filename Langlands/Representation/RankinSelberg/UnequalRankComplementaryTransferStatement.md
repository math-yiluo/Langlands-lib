# Paired complementary-block transfer

Worker 396 designed this internal interface for same-multiplier propagation.
Worker 467 independently checked the original sources and integral definitions,
and prepared this statement and its expanded documentation. The topological,
field, measure and representation telescope and the private valuative-topology
helper are adapted from Worker 331's published
`UnequalRankGammaPropagationStatement`. Worker 331's setup in turn follows
Worker 11's published `FunctionalEquationStatement`.

`Langlands.RankinSelberg.UnequalRankComplementaryTransferStatement.{uF,uV,uW}
F T n r` is a proposition definition. This module states the paired transfer;
it does not prove it. The assertion is an internal sufficient consequence of
the root/Fourier induction used in JPSS §2.8, printed p.395, rather than a
named assertion in the original article.

## Data and quantifier order

The parameters are any prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural numbers `n,r`. The proposition installs
exactly the structures and quantifies over exactly the data of the published
`UnequalRankGammaPropagationStatement`, through its nonzero-functional clauses:

- the topology, valuative relation and local-field structure supplied by `T`,
  the induced additive uniform and nonarchimedean structures, and the Borel
  structures on the field, `GL_(n+1)`, its upper unipotent subgroup and its
  left-unipotent quotient;
- every `hnr : n < r`, unitary additive character `ψ`, and right-invariance
  instance for `unipotentHaar F.Carrier n`;
- every measure `μ` on `LeftUnipotentQuotient n F.Carrier` satisfying
  `IsCompatible` with the supplied actual `generalLinearHaar` and
  `unipotentHaar` measures;
- every supplied scalar `ν : AdditiveHaarMeasure F.Carrier` with
  `IsSelfDual ψ ν`;
- independent complex representation carriers `V : Type uV` and `W : Type uW`,
  with their additive-group and complex-module structures;
- actual representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)`, of
  Whittaker type for `standardCharacter ψ r` and
  `inverseStandardCharacter ψ n`, respectively;
- every specified `ℓ : glFunctionals ψ r π` and
  `ℓ' : glInverseFunctionals ψ n σ`, with `ℓ.val ≠ 0` and `ℓ'.val ≠ 0`.

The private helper obtains the nonarchimedean additive structure from the
valuative topology using Mathlib's basis of open submodules. It introduces no
extra hypothesis. The field and carrier universe parameters `uF,uV,uW` remain
independent. The proposition retains Whittaker-type scope, including reducible
representations allowed by that predicate.

After all these data, the assertion quantifies over every `j k : ℕ`,
`hr : r = n + (j + k + 2)`, and actual coefficients
`f : (coefficientModel π ℓ).toSubmodule` and
`f' : (coefficientModel σ ℓ').toSubmodule`. It then chooses **one**
`f₀ : (coefficientModel π ℓ).toSubmodule`, followed by real bounds `a,b`.
This coefficient belongs to the same original image model, not merely the
ambient Whittaker-function space. It may depend on `f,f'`, the blocks and all
earlier data. The same `f₀` must satisfy both of the following clauses.

## The two actual-integral equalities

Write `abv = normalizedAbsoluteValue T` and suppress the unchanged parameters
`ψ,abv,μ,π,σ,ℓ,ℓ'`. This notation abbreviates the following literal Lean APIs;
it does not replace them by an abstract integral family.

For every `s : ℂ` with `a < s.re`,

```text
unequalRankIntegralAt (j+1) k     ... f.val  f'.val s
  = unequalRankIntegralAt j (k+1) ... f₀.val f'.val s.
```

The rectangular measures are, respectively,
`rectangularMeasure ν (j+1) (n+1)` and
`rectangularMeasure ν j (n+1)`. Both use the same supplied `ν` and the same
quotient measure `μ`. The proofs passed to the integral wrappers derive the
two rank identities from `hr`; they add no mathematical assumption.

For every `s : ℂ` with `b < s.re`,

```text
dualUnequalRankModelIntegralAt hnr (j+1) k     ... f  f' s
  = dualUnequalRankModelIntegralAt hnr j (k+1) ... f₀ f' s.
```

The published definition of `dualUnequalRankModelIntegralAt` keeps all the
actual transformed data. On the left its complementary rectangular block
has `k` rows, and on the right it has `k+1` rows, with measures
`rectangularMeasure ν k (n+1)` and
`rectangularMeasure ν (k+1) (n+1)`. Both dual integrals use the inverse
character `ψ.scale (-1)`, the same `abv` and `μ`, and right translation of
`firstDualFunction ψ r` by the actual `blockWeylAt n r hnr`, representing
`diag(I_(n+1), w_(r-n))`. The second transformed coefficient is the unchanged
`secondDualFunction ψ n f'.val`. These first and second dual functions are
the long-Weyl inverse-transpose transforms: on a matrix `g` the underlying
function is evaluated at `weylLong * inverseTranspose g`. In particular, the
first coefficient on the right is the actual dual transform of the already
chosen `f₀`.

The bounds are separate, and equality is required only on the respective
right half-planes. Neither coefficient nor bound may depend on `s`.
The conclusion contains no residue cardinality `q`, rational function,
scalar multiplier, changed measure, or all-`s` equality. There is no
functional equation, continuation, common-generator, analytic or
irreducibility assumption. Subject only to the data hypotheses above,
this is an unconditional transfer target.

## Derived provenance and future proof obligations

JPSS Theorem 2.7, printed pp.390–391, treats representations of Whittaker type.
Its unequal-rank formula (2) uses complementary blocks and the right-translated
dual Whittaker function. The source ranks `r_source,t_source` correspond to
Lean `r+1,n+1`. Thus the adjacent original blocks `j+1` and `j` in this
statement correspond to complementary dual blocks `k` and `k+1`.

JPSS §2.8, printed p.395, reduces the functional equation to block zero and
states that the proportionality constant stays the same when passing between
blocks. For a rank-one test it refers to JPS1979 Theorem 4.5; for general test
rank it replaces JPS1979 Lemma 4.1.5 by the Fourier cutoff lemma on JPSS
pp.394–395. That lemma transfers an upper-column Fourier smear to a cutoff
on the integrated lower row.

In the induction step of JPS1979 Theorem 4.5, printed pp.197–198, a lower-row
average by compactly supported right translates produces a new Whittaker
coefficient. Choosing a sufficiently large compact-open cutoff makes its
original integral at the smaller row block equal the original coefficient's
integral at the larger row block. The dual transform of that **same** average
is an upper-column Fourier smear. Fourier transfer gives a small-support
cutoff in the complementary dual row; smoothness removes this cutoff and
recovers the dual integral of the original coefficient at the smaller
complementary block. Reversing equality gives exactly the two orientations
stated here. This is the source rationale for the paired internal interface,
not an assertion that the source states this Lean predicate verbatim.

The future proof must perform both transfers on the actual coefficient image,
justify every integral interchange and each right-half-plane bound, and show
that one averaged coefficient works for both clauses. Self-duality of the
**supplied** `ν` must account for the Fourier cutoff's volume and every
Fourier scaling; no independently normalized measure or unexplained scalar
may replace it. `rectangularMeasure` is the iterated finite product of that
scalar measure. The zero-row cases use the published unit point mass, so
`j=0` or `k=0` causes no new normalization choice.

Uniform rectangular support, finite Schwartz expansion, upper-column
smearing and its global and pointwise Fourier identities are separate future
proof inputs. They are neither assumptions of this statement nor proved by
this module. The paired equalities suffice for a future same-multiplier
propagation argument to transport existing continuations with the identical
rational functions on their respective half-planes; this module supplies
neither those continuations nor that propagation proof.

## Originals

- `jpss-1983-rankin-selberg`: H. Jacquet, I. I. Piatetski-Shapiro and
  J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of
  Mathematics 105 (1983), 367–464. Theorem 2.7 pp.390–391, Fourier cutoff
  lemma pp.394–395, and §2.8 p.395.
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
  SHA256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- `jps-1979-gl3-i`: H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic Forms on GL(3) I*, Annals of Mathematics (2) 109 (1979),
  169–212. Proof of Theorem 4.5, induction step pp.197–198.
  Retained original:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
  SHA256: `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

Both retained originals were read at the listed pages. No source-specific
erratum note was present in the checked project and published Library
`notes/errata` locations. This check records the available errata context;
it does not certify that no erratum exists elsewhere.
