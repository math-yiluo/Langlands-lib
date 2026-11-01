# The polynomial-cleared first-block Laurent identity

Authors: Worker 1206 (Lean and initial Markdown) and Worker 1191 (source and
API audit, normalization analysis and Markdown refinements).

`Langlands.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement.{uF,uV,uW}`
is a closed proposition definition for the first-block calculation behind JPSS
(1983), Section 4.7 equation (1), printed page 412, with its functional-equation
calculation in Section 4.9, printed pages 416–418. This file states the analytic
identity; it does not prove it.

## Source and provenance

The registered original is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source passages read are Section 4.1, printed page 406, and Sections 4.6–4.9,
printed pages 411–418 (one-based PDF pages 41 and 46–53). Printed page 410
supplies the start of the opposite-twist construction. No applicable registered
erratum was located in the source index or project and Library notes.

Section 4.1 supplies the module of bilateral formal Laurent series, explicitly
allowing polynomial torsion. Section 4.6 supplies the upper unfolding and
Section 4.7 supplies the lower integral. Section 4.9 applies the functional
equation to the original first block. Expressing that calculation using the
Library's finite Laurent convolution, retaining normalized-generator
polynomials and quantifying over all compatible normalized quotient measures,
is derived formal packaging of the source calculation. The source does not
state this Lean telescope or the polynomial-cleared formula in these terms.

## Parameters and order of quantifiers

For every prime `p` with `Fact p.Prime` and every `F : PadicField.{uF} p`, the
statement uses the canonical topology, valuation, local-field, Hausdorff,
second-countable and Borel structures. `UnitaryAdditiveCharacter` includes
continuity and nontriviality. Every such character `ψ` and every supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` are
retained. The self-dual additive Haar measure is `ν.val`.

Take all `t`, `m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`. Thus the test
rank is exactly `t + 1`, and the blocks have arbitrary positive sizes
`a = m 0 + 1`, `b = m 1 + 1`, including size one. The proof term `hlt : m 0 < t`
is obtained from `h` by expanding the two-term sum and natural-number
arithmetic; it is not an additional hypothesis. The test carrier `V : Type uV`
and dependent block carriers `W i : Type uW` have universes independent of the
field universe `uF` and each other.

The representation `π` on `GL_(t+1)(F)` has full standard Whittaker type.
Every supplied `lambda : Whittaker.glFunctionals ψ t π` is quantified. The
dependent family `τ i` has full standard Whittaker type in each block, and all
supplied `ell i : Whittaker.glInverseFunctionals ψ (m i) (τ i)` are retained.
No irreducibility or nonzero-functional hypothesis is imposed. Only after all
these inputs does the statement choose one real `C`. For every `u > C` it uses
exactly `σu = twoBlockOppositeTwistBlocks F m τ u` and
`ellu i = twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)`, with twists
`(-u,+u)`. The bound can depend on `π` and all preceding data, but precedes
quotient measures, epsilon monomials, sections, vectors, Schwartz functions and
slice integers.

## Measures and actual coefficient functions

The statement fixes `G = GL_(t+1)(F)`, `N = upperUnipotent (t+1) F.Carrier`,
`GA = GL_a(F)` and `NA = upperUnipotent a F.Carrier`. Their Haar measures are
exactly `generalLinearHaar F.Carrier t`, `unipotentHaar F.Carrier t`,
`generalLinearHaar F.Carrier (m 0)` and `unipotentHaar F.Carrier (m 0)`, with
integral-points mass one. It asserts right-invariance certificates for both
unipotent measures and existence of compatible measures on
`NQ = LeftUnipotentQuotient t F.Carrier` and
`AQ = LeftUnipotentQuotient (m 0) F.Carrier`. Compatibility is the actual
`QuotientIntegration.IsCompatible` for these group and unipotent measures.
The conclusions quantify over **every** compatible pair `νN, νA`, after `C`
and `u`, and assert sigma-finiteness of both and of the transported lower measure.
Existence and right invariance are unconditional and precede the representations.

The upper quotient `HQ` is
`TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier`; the lower quotient `LQ`
is `TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier`. All quotient
measurable spaces in the statement are their Borel spaces. Put
`μR = rectangularMeasure ν.val a b`. For each actual section
`f : TwoBlockJacquet.Sections F h σu`, each vector in the actual coefficient
image `(Whittaker.coefficientModel π lambda).toSubmodule`, and each row
Schwartz–Bruhat function `Φ`, the statement uses precisely

```text
Eup  = TwoBlockUnfolding.integrand ellu f Wtest.val Φ
Aup  = TwoBlockUnipotentQuotient.radicalAverage F h μR Eup
Elow = TwoBlockLowerUnfolding.integrand ellu f Wtest.val Φ ν.val
νMinus = Measure.map
  (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN.
```

The published theorem `TwoBlockUnfolding.radicalAverage_integrand_mk` gives,
at every representative `g`,

```text
Aup [g] =
  Wtest(g) *
    TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g *
    Φ(lastRow g).
```

This is an identity of total integrals, with no convergence hypothesis; the
statement separately requires absolute integrability on every slice for
`u > C`. The original and transported functionals have the same underlying
linear maps. The lower function is the actual descent of
`Wtest(Crot*g)` times the scalar section at `g` times the published plus-sign
first-block partial row Fourier transform of `gΦ`, where
`B = succBlockShape m h` and `Crot = (B.reverseMatrix F.Carrier)⁻¹`.
The map `lowerToStandard` is `[g] ↦ [Crot*g]`; its inverse transports `νN`
to `νMinus`. This is left multiplication on quotient classes, not quotient
conjugation.

For every `f, Wtest, Φ`, the unconditional clause asserts `Measurable Aup`,
`Measurable Elow` and, for every integer `k`, `Integrable Aup` on the
`νN`-restricted standard determinant slice and `Integrable Elow` on the
`νMinus`-restricted lower determinant slice. These are genuine absolute
integrability assertions about complex-valued functions. The same `C` works
for all inputs, including zero inputs, without any epsilon certificate.
The coefficient functions are elements of `BilateralLaurentSeries = ℤ → ℂ`:

```text
Zup k  = ∫ q, Aup q ∂νN.restrict (RankinSelberg.determinantSlice T t k)
Zlow k = ∫ z, Elow z
  ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k).
```

## Conditional common epsilon witnesses and finite action

Separately from convergence, for every `cε : ℂˣ` and `d : ℤ`, the conclusion is
conditional on the supplied concrete predicate

```text
UnequalRankEpsilonEquation hlt q ψ (normalizedAbsoluteValue T)
  νA ν.val π (σu 0) lambda (ellu 0) cε d,
```

where `q = T.residueCardinality`. This is an input internal to this closed
prerequisite. The parent assembly must discharge generic small-block
functional-equation existence from its separately proved inputs.

The conclusion chooses common `ζ : ℂˣ` and `P Pdual : Polynomial ℂ` before
any section, vector or Schwartz test. It asserts the actual
`HasModelMinusOneScalar (σu 0) (ellu 0) ζ`. Its next conjunct repeats the
**entire body** of `UnequalRankEpsilonEquation` with those same witnesses:
for every `j, k : ℕ` with `hr : t = m 0 + (j + k + 1)`, `P` is the normalized
generator for `unequalRankValuesAt` using the actual rectangle product
measure, `Pdual` is the normalized generator for
`dualUnequalRankRationalValuesAt`, and for every actual coefficient pair
there are rational continuations `R, Rdual` satisfying
`NormalizedFunctionalEquation q P Pdual ζ cε t d R Rdual`.
Each `HasRationalContinuation` asserts agreement of the actual integral with
the rational function on a right half-plane, with the denominator nonzero
throughout that half-plane. In
`IsNormalizedGenerator values P`, normalization means exactly `P.coeff 0 = 1`
and

```text
zetaSpan values =
  Submodule.span LaurentCoefficients
    {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹}.
```

Thus the reciprocal `1/P` generates the actual Laurent-coefficient module of
rational integral values. Both `P` and `Pdual` carry this assertion, rather
than merely clearing some denominators.

The original block used by Section 4.9 is `j = m 1 = b - 1`, `k = 0`;
`h` gives `t = m 0 + (m 1 + 0 + 1)`. Keeping all complementary blocks also
retains that original block when either block has size one.

With exactly these witnesses and for every `f, Wtest, Φ`, the final conjunct is

```text
D • Zlow =
  (LaurentPolynomial.C ((ζ : ℂ)^t * (cε : ℂ)) *
    LaurentPolynomial.T d * P.toLaurent) • Zup,
D = Polynomial.eval₂ LaurentPolynomial.C
  (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) Pdual.
```

Thus `D` is exactly `Pdual(q⁻¹ X⁻¹)`. The exponent is `t` because the actual
test rank is `t + 1`. The action is the published finite convolution on
bilateral coefficient functions: `(Q • Z)(n) = ∑ i ∈ Q.coeff.support,
Q.coeff i * Z(n-i)`. It is an equality of all coefficients, with no annular
evaluation, rational multiplication on bilateral series, or unrestricted
bilateral product.

`NormalizedFunctionalEquation` puts the dual polynomial and dual continuation
on the left and `ζ^t cε X^d` times the original normalized integral on the
right. In the same notation, the source's equation (4.7.1) has orientation

```text
(C(cε) * T(d) * P.toLaurent) • Zup = (C(ζ^t) * D) • Zlow.
```

The normalized-generator certificate forces the first-block coefficient
model to be nonzero: a zero model has only zero rational integral values and
cannot generate the nonzero module spanned by `1/P`. On this nonzero model,
apply `HasModelMinusOneScalar` twice to a nonzero coefficient value. Since
`(-I)^2 = I`, the actual operation `f(g) ↦ f((-I)g)` is an involution and
`ζ² = 1`. Multiplying the source identity by the scalar `ζ^t` therefore
gives the orientation in the statement, with the same `ζ^t` factor. This
argument uses only the actual coefficient image; it does not presume a
central character on a reducible original carrier. It cancels no polynomial.

Zero supplied functionals are allowed in the unconditional convergence
clause; if `lambda` or either `ell i` is zero, the corresponding actual
integrands vanish. For zero `lambda` or zero `ellu 0`, the small coefficient
value set is zero, so a normalized generator (whose constant coefficient is
one and which generates the stated fractional ideal) does not exist. The
statement does not assert that an epsilon certificate exists in that case.
Its witness and identity clause is conditional on that certificate. If only
the second block functional vanishes, the two large integrands vanish and
the identity still holds whenever the small-block certificate is supplied.

The polynomials are the actual normalized generators, rather than arbitrary
denominators or the reduced numerator and denominator of gamma. Section 4.1
permits polynomial torsion: the published bilateral module has, for example,
the nonzero constant coefficient function annihilated by `1 - X`. Cancelling
any common polynomial factor in this identity needs a separate argument.

## Normalization route and proof boundary

The later proof must implement the following measure comparison. Write `O`
for the canonical valuation ring and

```text
cR = μR {x | ∀ i j, x i j ∈ O} = (ν.val O)^(a*b).
```

This mass is positive and finite; it is generally not one because the
supplied self-dual measure depends on `ψ`. Scalar comparisons of complex
integrals use `cR.toReal`.

1. The first Section 4.6 unfolding, in
   `TwoBlockFixedSliceUnfoldingStatement`, relates the upper coefficient to
   the integral of `Eup` on the upper block quotient by
   `Zup k = cR.toReal • ∫ Eup`. The integral is restricted to the inverse
   image of the standard determinant slice. The factor records the
   difference between the supplied rectangular product measure and the
   integral-points mass-one measure on the full upper unipotent group.
2. Section 4.6 equation (6), in
   `TwoBlockFirstBlockQuotientIntegrationStatement`, disintegrates that
   upper block-quotient integral into first-block fibers over the mixed
   quotient. This formula has no determinant density.
3. Section 4.9 equation (2), in
   `TwoBlockLowerFirstBlockQuotientIntegrationStatement`, relates the
   iterated lower-radical integral to `cR.toReal` times the mixed-quotient
   integral. It uses the one lower mixed Haar measure giving its integral
   points mass one. The lower `b × a` rectangle and the upper `a × b`
   rectangle have the same product-cube mass. Solving this comparison for
   the mixed-quotient integral uses the reciprocal scalar and cancels the
   first unfolding's `cR.toReal`.
4. Split the lower rectangle into a `(b-1) × a` variable and an
   `a`-dimensional row. The first variable supplies the original small
   functional equation with `j = b-1` and `k = 0`; the row carries the
   supplied self-dual product measure for the plus-sign partial Fourier
   transform. Section 4.9 equation (8) then identifies the lower
   first-block iterated integral with the lower quotient coefficient with
   density `|det v|^b = q^(-k*b)` on the first-block determinant slice of
   index `k`. There is no rectangular cube factor in equation (8).

These comparisons explain the normalization required in the future proof;
they are not additional conjuncts or a proof of this statement. In
particular the supplied Fourier measure remains explicit throughout, and
the finite Laurent identity contains no extra scalar or renormalization.

This proposition does not supply the analytic proof. It also does not establish
the Section 4.8 analytic companion comparison, the strictly dominant analogue
of Section 4.10, two-block factor multiplicativity, polynomial-cleared
deformation specialization, or either dominant-rank base theorem. It imports
no unrestricted multiplicativity, finite-block parent, Section 7 assembly,
Section 9.3, or later result depending on these bases.
