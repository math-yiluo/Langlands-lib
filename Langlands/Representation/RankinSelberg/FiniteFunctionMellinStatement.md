# Finite-function Mellin integrals on a p-adic torus

`Langlands.RankinSelberg.FiniteFunctionMellinStatement` is a Prop-valued
statement, with no proof supplied. It isolates the analytic input obtained by
grouping the finite-function tensor reduction and the one-variable Mellin
argument used consecutively in the proof of JPSS Theorem (2.7)(i)-(ii).
It is a derived interface to that argument, not a verbatim named theorem of
the source.

## Exact scope and conventions

The declaration quantifies over every prime `p`, every `F : PadicField.{uF} p`,
every supplied `T : F.TopologicalData`, every natural dimension `r`, and every
weight function `m : Fin r → ℕ` with `0 < m i` for all `i`. It installs
`T.topology`, `T.valuativeRel`, and `T.localField`, and the Borel measurable
structures on the field and its unit group. Function spaces have the finite
product topology and product measurable structure. No canonical replacement
for the supplied `T` is made.

Write `A = Fin r → F.Carrierˣ`. Its measure is the actual product
`Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)`. Each factor assigns
mass one to the integral units, by
`localMultiplicativeHaar_integerUnits` in `RankinSelberg.Measures`. The
absolute value is `T.normalizedAbs`, normalized using the residue cardinality
`q = T.residueCardinality`, rather than the base prime or an unnormalized
extension absolute value.

A finite function `η : A → ℂ` means exactly that it is continuous and that

```text
Submodule.span ℂ (Set.range (fun b : A => fun a : A => η (b * a)))
```

is finite-dimensional over `ℂ`. This is the same translation-finiteness
condition as in `Langlands.WhittakerTypeAsymptoticStatement`, applied to this
supplied topology and torus. A character decomposition is not a hypothesis.

For a finite set `X` of such functions and any
`Φ : HarmonicAnalysis.SchwartzBruhat (Fin r → F.Carrier)`, define locally

```text
I(η, Φ, s, a) = Φ((↑(a i))ᵢ) η(a) ∏ᵢ (T.normalizedAbs ↑(a i) : ℂ)^((m i : ℂ) * s),
M(η, Φ, s) = ∫ a, I(η, Φ, s, a) ∂dA.
```

Here the power is the complex power and the integral is the actual Bochner
integral. The proposition has three conclusions:

1. For every `η ∈ X` and every `Φ`, the integrand is `MeasureTheory.Integrable`
   for all `s` in some right half-plane. The half-plane may depend on `η` and
   `Φ`.
2. For every such pair there exists `R : RationalFunctions` satisfying
   `HasRationalContinuation q (M(η, Φ, ·)) R`. This relation includes both
   agreement at `q^(-s)` and nonvanishing of the reduced denominator throughout
   a right half-plane. Its half-plane can be intersected with the convergence
   half-plane; neither equality nor convergence is an input assumption.
3. `HasCommonDenominator` holds for the set of **all** rational continuations
   obtained as `η` ranges over `X` and `Φ` ranges over the whole Schwartz–Bruhat
   space. Thus there is one nonzero `d : LaurentCoefficients` such that, for
   every such continuation `R`, some Laurent polynomial `P` satisfies
   `laurentToRatFunc P = laurentToRatFunc d * R`. The denominator can depend on
   `F`, `T`, `r`, `m`, and `X`, but is independent of `Φ` and uniform over `X`.

The finite set `X` is quantified before every test function. The test functions
are arbitrary compactly supported locally constant functions, with no
restriction to decomposable tensors. All auxiliary predicates, functions, and
sets are local let-bindings; this file adds just the single public proposition.

The dimension `r = 0` is included. Then `A` is a singleton, the product measure
is its unit point mass, the weight product is one, and the integral is constant
in `s`. Positivity of the weights is vacuous in this case.

## Original sources and derivation

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
  Convolutions*, American Journal of Mathematics **105** (1983), 367–464:
  proof of Theorem (2.7)(i)-(ii), printed pp. 391–392, especially p. 392,
  displays (5)–(6) and the following convergence and common-denominator
  paragraphs. Registered source `jpss-1983-rankin-selberg`, retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
  GL(3) I*, Annals of Mathematics (2) **109** (1979), 169–212:
  §2, especially the definition of finite functions before Proposition (2.2)
  on printed p. 181 and Lemma (2.2.1) on p. 182 (context begins on p. 180).
  Registered source `jps-1979-gl3-i`, retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

JPS gives the precise continuity plus finite translation-span definition; its
Lemma (2.2.1) explains the surrounding finite-function expansion framework.
That lemma is not itself a Mellin-integral theorem and is not assumed here.
JPSS p. 392 writes each relevant finite function as a finite sum of products
of one-variable finite functions, then reduces Schwartz functions on the
product to finite tensor sums. The resulting factors in (6) are one-variable
Mellin integrals. JPSS then states their convergence for large real part and
rationality with denominator controlled by the finite functions, obtaining a
common denominator independent of the varying test functions.

This declaration packages those two reductions into an `r`-variable assertion
for an arbitrary fixed finite family of finite functions. The positive
integer weights generalize the exponents `1, …, r` in (6); in zero-based Lean
indexing the JPSS choice is `m i = i.val + 1`. Substituting `m i * s` into each
one-variable integral preserves a common right half-plane because every
weight is positive, and changes the rational parameter to a positive integer
power of `q^(-s)`. The resulting denominators remain Laurent polynomials.
A finite collection of tensor factors for the fixed finite set `X` then
provides a single common denominator. These are the mathematical derivation
and intended future proof obligations, not a claim that these reductions
have already been formalized.

Fixed spectral shifts and modulus factors may be absorbed into `η` when their
preservation of continuity and translation-finiteness has separately been
proved. No Whittaker expansion, convergence, rationality, denominator bound,
or normalized-generator existence is assumed in this statement. It makes no
claim about generating a fractional ideal by a normalized reciprocal
polynomial. The zero-dimensional extension is the direct singleton case,
rather than an additional assertion quoted from JPSS.
