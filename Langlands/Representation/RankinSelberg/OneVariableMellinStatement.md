# Weighted one-variable Mellin analysis

`Langlands.RankinSelberg.OneVariableMellinStatement.{uF}` is a
Prop-valued definition. This module states the one-variable analytic input
for the finite-function Mellin argument; it supplies no proof. It is a
derived interface to the argument in JPSS (1983), printed p. 392, rather
than a separately named theorem quoted from that article.

## Exact scope

The proposition quantifies over every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every
natural weight `m` with `0 < m`, and every function `η : F.Carrierˣ → ℂ`
that is continuous and has finite-dimensional complex left-translation
span:

```text
Submodule.span ℂ
  (Set.range (fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))).
```

These are the only hypotheses on `η`. In particular, no quasicharacter or
character-polynomial decomposition is supplied as an input. The translation
convention is immaterial to the source definition on this abelian group,
but the displayed left-translation formula is the exact Lean convention.

The local instances are `T.topology`, `T.valuativeRel`, `T.localField`, and
the Borel measurable structures and `BorelSpace` witnesses on `F.Carrier`
and `F.Carrierˣ`, exactly as in `FiniteFunctionMellinStatement`. The field
universe remains arbitrary. The field scope is finite extensions of
`ℚ_p`; the original nonarchimedean argument has wider field scope.

The measure is the actual `localMultiplicativeHaar F.Carrier`. Its
normalization assigns mass one to the integral units, as proved by
`localMultiplicativeHaar_integerUnits` in `RankinSelberg.Measures`. The
absolute value is `T.normalizedAbs`, with residue cardinality
`q = T.residueCardinality`. In particular the spectral variable is
`q^(-s)` for the residue field of `F`, not the base prime `p`.

For each `Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier`, the proposition
defines locally

```text
I(Φ,s,a) = Φ(↑a) * η(a) * (T.normalizedAbs ↑a : ℂ)^((m : ℂ) * s),
M(Φ,s)   = ∫ a : F.Carrierˣ, I(Φ,s,a) ∂localMultiplicativeHaar F.Carrier.
```

The power is complex exponentiation, and the integral is the actual
Bochner integral. The test functions range over the full space of compactly
supported locally constant functions on the field, including those nonzero
at zero. The conclusions form a conjunction:

1. For every `Φ` there is a real bound `c` such that `I(Φ,s,·)` is
   `MeasureTheory.Integrable` whenever `c < s.re`. This is actual
   integrability, not merely a property of the totalized integral.
2. For every `Φ` there is `R : RationalFunctions` with
   `HasRationalContinuation q (M(Φ,·)) R`. This unchanged relation requires
   agreement with `RatFunc.eval` at `spectralPoint q s` and nonvanishing
   of the reduced denominator there throughout some right half-plane.
   Its threshold and the integrability threshold may differ; taking
   their maximum gives a common domain.
3. `HasCommonDenominator` holds for the set
   `{R | ∃ Φ, HasRationalContinuation q (M(Φ,·)) R}`.
   Thus one nonzero `d : LaurentCoefficients` satisfies, for every
   rational continuation `R` of every test function, an identity
   `laurentToRatFunc P = laurentToRatFunc d * R` for some Laurent polynomial
   `P`. The denominator may depend on `F`, `T`, `m`, and `η`, but is
   independent of `Φ`. This quantifies over all continuations, rather
   than selecting a witness separately for each test function.

Every auxiliary function and set is a local let-binding. The sole new
public declaration is the proposition itself. Neither analytic existence
nor a denominator certificate is assumed. No normalized generator or
representation-theoretic assertion is included.

## Original sources and derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
  (1983), 367–464, proof of Theorem (2.7)(i)–(ii), printed pp. 391–392,
  especially display (6) and the subsequent convergence, rationality,
  and common-denominator paragraphs on p. 392. Registered source:
  `jpss-1983-rankin-selberg`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
  *Automorphic forms on GL(3) I*, Annals of Mathematics (2) **109**
  (1979), 169–212, §2, printed pp. 180–182, especially the definition
  of finite functions immediately before Proposition (2.2), p. 181.
  Registered source: `jps-1979-gl3-i`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`;
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

The cited originals were read directly; JPSS pp. 391–392 and the JPS
definition on p. 181 were also inspected visually. Neither the project
nor the supplied Library had a `notes/errata` directory when checked on
2026-10-25.

JPS defines a finite function on a locally compact abelian group by
continuity and finite-dimensional translation span. Its Lemma (2.2.1)
on p. 182 concerns the surrounding finite-function expansion argument;
it is not itself the Mellin theorem asserted here.

JPSS first separates the finite functions and Schwartz functions into
finite tensor sums. Display (6) consists of one-variable integrals with
positive integer weights `i`. The following paragraphs assert convergence
for large real part, rationality in `X = q^(-s)`, and control of denominators
by the finite functions, yielding a common denominator independent of
the varying Schwartz functions.

Here an arbitrary positive integer `m` generalizes those weights.
Mathematically, applying the unweighted assertion at the parameter `m*s`
preserves a right half-plane because `m > 0`; the rational variable
becomes `X^m`. Substitution of `X^m` sends a nonzero Laurent polynomial
to a nonzero Laurent polynomial, so the desired denominator remains
uniform over the test functions. This explains the derived formulation;
it does not claim a formal proof of the rescaling or analytic assertions.

Only one finite function is needed in this statement. In the
multivariable application, tensor decompositions of a fixed finite family
produce finitely many one-variable finite functions, so the parent proof
can combine their denominators. Proving those decompositions and the
tensor/Fubini assembly is separate from proving this proposition.

## Remaining proof obligation

A future proof must derive convergence, continuation, and the uniform
denominator from continuity and translation-finiteness. Possible routes
include valuation-shell recurrences for finite-dimensional translation
operators, or a separately proved character-polynomial decomposition.
No such route is implemented or assumed here. Compilation checks that
the declaration is a well-formed proposition; it does not establish the
mathematical theorem.

Worker 351 authored this pair using Worker 352's supplied formulation.
