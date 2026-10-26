# Continued unequal-rank bilinear forms at block zero

This module defines the proposition
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement.{uF,uV,uW} F T n r`
and the fixed-data proposition
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsConclusion`.
It is a derived conditional interface for the actual original and reflected
dual JPSS integrals. It is a statement only: it proves neither the analytic
inputs, bilinearity or covariance of continued integrals, full Whittaker-type
uniqueness, nor existence of gamma or epsilon factors.

## Universal data and hypotheses

For every natural number `p`, instance `[Fact p.Prime]`, p-adic field
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and natural numbers
`n,r`, the statement installs the same structures as
`UnequalRankBlockZeroGammaExistenceStatement`: `T.topology`,
`T.valuativeRel`, `T.localField`, the right uniform space of the additive group,
its uniform additive group structure, and the nonarchimedean additive group
structure derived from the valuative topology. It installs the Borel measurable
spaces and Borel-space instances on `F.Carrier`, `GeneralLinear (n+1) F.Carrier`,
`upperUnipotent (n+1) F.Carrier`, and `LeftUnipotentQuotient n F.Carrier`.
The local bridge lemma proves the additive nonarchimedean instance using the
basis of open submodules of the valuation ring.

It then quantifies, in order, over:

1. A proof `hnr : n < r` and a unitary additive character `ψ` of `F.Carrier`.
2. An instance asserting right invariance of `unipotentHaar F.Carrier n`,
   and a measure `μ` on the actual quotient
   `LeftUnipotentQuotient n F.Carrier = N_(n+1) \ GL_(n+1)`.
   The measure must satisfy
   `IsCompatible (upperUnipotent (n+1) F.Carrier)
   (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ`.
3. A supplied scalar additive Haar measure `ν : AdditiveHaarMeasure F.Carrier`.
   Self-duality is not required for this covariance construction.
4. Independent carriers `V : Type uV` and `W : Type uW`, each with an
   additive commutative group and a complex module structure.
5. Representations `π` of `GL_(r+1)` on `V` and `σ` of `GL_(n+1)` on `W`,
   with the full hypotheses
   `IsOfWhittakerType r (standardCharacter ψ r) π` and
   `IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`.
6. Functionals `ℓ : glFunctionals ψ r π` and
   `ℓ' : glInverseFunctionals ψ n σ`, both nonzero as linear maps.

The Whittaker-type predicate retains admissibility, including smoothness,
finite generation over the group algebra, and a functional space linearly
equivalent to `ℂ`. No irreducibility or central-character hypothesis is added.
The universes `uF`, `uV`, and `uW` remain independent.

Put `k = r-n-1`, let `hr : r = n + (0+k+1)` be the dimension equality
derived from `hnr`, and set `q = T.residueCardinality` and
`abv = normalizedAbsoluteValue T`. The two analytic premises are exactly:

```text
UnequalRankAnalyticAt 0 k hr q ψ abv μ
  (rectangularMeasure ν 0 (n+1)) π σ ℓ ℓ'

UnequalRankAnalyticAt k 0 (by omega) q (ψ.scale (-1)) abv μ
  (rectangularMeasure ν k (n+1))
  (inverseTransposePullback π) (inverseTransposePullback σ)
  (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
```

They are explicit conditional hypotheses, not axioms or claims that the
analytic theorem has been proved. Each input includes convergence on a
right half-plane for every pair of model vectors, rational continuation,
its own common denominator, and a normalized generator for its own block.
There is no premise asserting a common generator across different blocks.

## The two actual integral families

Write `M = (coefficientModel π ℓ).toSubmodule` and
`M' = (coefficientModel σ ℓ').toSubmodule`. For every `f : M` and `f' : M'`
the original, unreflected family is

```text
I(f,f') =
  unequalRankIntegralAt 0 k hr ψ abv μ
    (rectangularMeasure ν 0 (n+1)) f.val f'.val.
```

This is the existing iterated JPSS integral with zero rectangular rows.
Its rectangular measure is exactly unit point mass; at a quotient representative
`g` the integrand is
`f(diag(g,I_(r-n))) f'(g) |det g|^(z-(r-n)/2)` at parameter `z`.
All matrices and quotient descent are those of `QuotientIntegrals`.

The dual family, also before reflecting its parameter, is

```text
D(f,f') =
  dualUnequalRankModelIntegralAt hnr 0 k hr ψ abv μ ν π σ ℓ ℓ' f f'
```

and by its existing definition is exactly

```text
unequalRankIntegralAt k 0 (by omega) (ψ.scale (-1)) abv μ
  (rectangularMeasure ν k (n+1))
  (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
    (blockWeylAt n r hnr))
  (secondDualFunction ψ n f'.val).
```

The first dual function is the actual Weyl/inverse-transpose transform
`g ↦ f(w_(r+1) (g^t)^(-1))`, and the second is its corresponding
smaller-rank transform. The first is additionally right translated by
the existing `blockWeylAt n r hnr = diag(I_(n+1),w_(r-n))`.
The complementary block is `(k,0)`, with `k` rectangular rows. Both integrals
use the same supplied compatible `μ` and the same scalar `ν`; the latter
defines the rectangular product measures without changing normalization.
The analytic dual premise uses the actual inverse-transpose representations
and their `firstDualFunctional` and `secondDualFunctional`. `DualModels`
supplies the corresponding model equivalences, including the translated first
model. No surrogate dual family is introduced.

## Uniform finite exceptional set and bilinear forms

The fixed-data conclusion has exactly the order

```text
∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
  ∃ B Bdual : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ, ...
```

Here `spectralPoint q s = (q : ℂ)^(-s)`. Thus `E` is a finite set of
spectral values, not a finite set of exponents `s`. It may depend on the
fixed data but is chosen before `s`, all model vectors, all rational
continuations, and all covariance translations. The two genuine curried
complex-linear maps may depend on `s`.

Both forms satisfy the already published, unchanged predicate
`IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s`.
For each form `C` this requires, for every `g : GL_(n+1)` and all model vectors,

```text
C (modelRepresentation π ℓ (diag(g,I_(r-n))) f)
  (modelRepresentation σ ℓ' g f')
  = determinantWeight abv g (((r-n : ℕ) : ℂ)/2 - s) * C f f'.
```

It also requires, for every `u : upperUnipotent (r+1)` whose leading
`(n+2)`-square block is the identity, and all model vectors,

```text
C (modelRepresentation π ℓ u.val f) f'
  = (standardCharacter ψ r u : ℂ) * C f f'.
```

The embedding is the predicate's actual `appendIdentity` followed only by
dimension reindexing. Its unipotent condition is exactly
`IsUnequalRankCovarianceUnipotent n u`, the actual `U_(n+2,r+1)` subgroup.
The two forms satisfy identical covariance at the same parameter `s`.

Separately, the conclusion requires each of the following universally
quantified implications:

```text
∀ (f : M) (f' : M') (R : RationalFunctions),
  HasRationalContinuation q (I(f,f')) R →
    R.denom.eval (spectralPoint q s) ≠ 0 ∧
    B f f' = RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R

∀ (f : M) (f' : M') (Rd : RationalFunctions),
  HasRationalContinuation q (D(f,f')) Rd →
    Rd.denom.eval (spectralPoint q (1-s)) ≠ 0 ∧
    Bdual f f' = RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1-s)) Rd.
```

Neither implication requires a continuation of the other integral. In the
dual clause the continuation is of `D` at its unreflected parameter; only its
evaluation uses `1-s`. Both evaluations are unnormalized and have no
polynomial multipliers. Regularity of every reduced denominator is part of
the conclusion. There is no assertion at excluded points and no use of
totalized evaluation at poles to justify bilinearity.

No bilinearity, covariance, bilinear uniqueness, nonzero form at each point,
comparison scalar, functional equation, or gamma/epsilon existence is a
premise. The finite exceptional set and both forms are conclusions.

## Provenance and original-source scope

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
(1983), 367–464, §2.11, printed pp.398–399, especially (2.11.1)–(2.11.4).
Registered source: `jpss-1983-rankin-selberg`, local PDF
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.398–399, one-based PDF pages 33–34, were visually read.
The current registration and project literature/Library note locations were
checked; no matching registered erratum was found there.

The source's large rank and small rank are `r+1` and `n+1` in Lean.
Formula (2.11.1) gives the original block-zero and reflected complementary
integrals. Formula (2.11.2) gives the common general-linear covariance with
exponent `(r-n)/2-s`. Formula (2.11.4) gives the unipotent covariance with
leading identity block of size `n+2`.

The separation of two analytic premises, their own common denominators,
one uniform finite spectral exceptional set, and independent evaluation
clauses is an internal derived interface for the block-zero gamma proof.
It is not a literal theorem statement from the source. A future proof must
construct rational bilinear values from actual integral linearity on
convergent half-planes, obtain denominator control, and establish covariance
by changes of variables for the supplied measures. This module does not
carry out those arguments.

The separate uniqueness Proposition on printed p.399 assumes irreducible
generic representations. It neither narrows this conditional construction's
full Whittaker-type scope nor proves full Whittaker-type uniqueness.
That uniqueness result, analytic continuation existence, and the subsequent
gamma-factor construction remain separate proof obligations.
