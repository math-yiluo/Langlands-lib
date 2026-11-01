# The strictly dominant first-block Laurent identity

Author: Worker 1206. The normalized-generator and sign explanation adapts
the published equal-rank source explanation by Workers 1206 and 1191.

`Langlands.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW}`
is a closed proposition definition for the first-block identity underlying JPSS
(1983), Section 4.10(2), printed page 419. It includes ordinary Jacquet
realization and genuine absolute integrability on every determinant slice.
This module states the analytic proposition and does not prove it.

## Source and derived packaging

The registered original is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The passages read for this statement are the first-block calculation in
Section 4.9, printed pages 416–418, and Section 4.10, printed pages 418–420
(one-based PDF pages 51–55). No applicable registered erratum was located in
the source index or the project and pinned Library notes checked.

Section 4.9 disintegrates the first-block quotient, applies the original
first-block functional equation, and integrates the resulting rectangular
variables. Section 4.10 adapts the calculation to a test representation of
strictly larger rank. Equation (2) on printed page 419 gives the lower
integral and its determinant exponent. Its original epsilon factor belongs
to the test representation paired with the first block.

The source illustrates the calculation with `k = 0`. Retaining every
complementary `j,k`, the actual five-block matrices, the two supplied-Haar
rectangle integrals, separate slice convergence conditions, all compatible
quotient measures, and zero supplied functionals is derived formal packaging
of that calculation. The finite Laurent identity with both actual
normalized-generator polynomials is also a derived formulation; the source
does not state this Lean telescope. None of these analytic extensions is
claimed to follow from the structural kernel definitions alone.

## Parameters and uniformity

The statement retains every prime `p` with `Fact p.Prime` and every
`F : PadicField.{uF} p`, with its canonical topology, valuation, local-field,
Hausdorff, second-countable and Borel structures. It retains every
`UnitaryAdditiveCharacter F.Carrier` (which includes continuity and
nontriviality) and every supplied
`ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ`, where
`T = F.canonicalTopologicalData`. Its scalar Haar measure is `ν.val`;
`q = T.residueCardinality` and `abv = normalizedAbsoluteValue T`.

Let `a = m 0 + 1`, `b = m 1 + 1`, and `a+b = t+1`, with `t<r`. The actual
test rank is `r+1`, the induced rank is `t+1`, and the actual block ranks are
`a,b`. The proof term `hlt : m 0 < r` follows from this two-term sum and
`t<r`; it is not an additional premise. The test carrier has universe `uV`
and the dependent block carriers have universe `uW`, independently of `uF`
and of each other.

The test representation `π` and both blocks `τ i` have full standard
Whittaker type. This permits reducible representations. Every supplied
`lambda : glFunctionals ψ r π` and every
`ell i : glInverseFunctionals ψ (m i) (τ i)` is retained, including zero.
After all representations and supplied functionals, the statement chooses
one `C : ℝ`. For every real `u>C`, it uses exactly

```text
σu = twoBlockOppositeTwistBlocks F m τ u
ellu i = twoBlockOppositeTwistFunctional F m ψ τ u i (ell i).
```

These are the opposite twists `(-u,+u)`, with the actual transported
functionals on the same underlying linear maps. The bound precedes all
quotient measures, epsilon certificates, sections, test coefficients,
complementary rectangles and determinant indices.

For every section `f` the statement asserts
`TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ellu i).val) μR f`,
where `μR = rectangularMeasure ν.val a b`. This means actual absolute
integrability of the ordinary Jacquet integrand at every ambient `g`.
It then chooses one
`J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu)`,
before every right-invariance certificate, quotient measure and test, with

```text
J.val (TwoBlockJacquet.inducedRep F h σu g f)
  = TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g.
```

This is a conclusion realizing the ordinary integral as a coefficient of an
inverse-character functional. It is not an assumed analytic identity.
The conclusion also requires `J.val ≠ 0` if both supplied `ell i` are
nonzero. General convergence and the coefficient law have no such premise.

## Exact measures and unconditional slice convergence

Write `G = GL_(t+1)(F)`, `N = upperUnipotent (t+1) F.Carrier`,
`GA = GL_a(F)`, `NA = upperUnipotent a F.Carrier`,
`NQ = LeftUnipotentQuotient t F.Carrier`,
`AQ = LeftUnipotentQuotient (m 0) F.Carrier`, and
`LQ = TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier`.
All the specified group, subgroup and quotient measurable spaces are Borel.
The group and unipotent measures are precisely

```text
μG  = generalLinearHaar F.Carrier t
μN  = unipotentHaar F.Carrier t
μGA = generalLinearHaar F.Carrier (m 0)
μNA = unipotentHaar F.Carrier (m 0).
```

These are the published integral-points mass-one normalizations.
The first conjunct asserts the existence of right-invariance certificates
for `μN,μNA` and compatible measures on both standard quotients.
The analytic conjunct, independently of those existential choices, retains
every supplied right-invariance certificate and every compatible pair
`νN : Measure NQ`, `νA : Measure AQ`. Compatibility is the actual
`QuotientIntegration.IsCompatible` with exactly these Haar measures.
It chooses no new quotient measure or rescaling and asserts sigma-finiteness
of `νN`, `νA` and the prescribed

```text
νMinus = Measure.map
  (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN.
```

For each `j,k : ℕ`, `hr : r=t+(j+k+1)`, actual section `f` and
`Wtest : (coefficientModel π lambda).toSubmodule`, put

```text
Wup  = Wtest.val transported by hr to rank index t+(j+k+1)
Wjac = (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val
μrect = rectangularMeasure ν.val j (t+1)
A = unequalRankAverage F j k ψ μrectBorel Wup Wjac 0
Zup = unequalRankSliceCoefficient F j k ψ νN μrectBorel Wup Wjac.
```

The coefficient API fixes the matrix Borel structure, while
`rectangularMeasure` uses the matrix product measurable structure. In Lean,
`μrectBorel` is exactly `μrect` transported along
`BorelSpace.measurable_eq` for the finite matrix space. These measurable
structures are equal because the canonical field is second countable.
This equality transport changes no measurable set mass and introduces no
map, scalar factor or measure choice. The product-space integrability clause
uses `μrect` in its original product structure.

Thus the rectangle is integrated first, and `Zup(a)` is the integral of
`A` on the standard determinant slice of index `a` against `νN`.
The integrand at zero retains the normalization
`-(j+k+1)/2`; zero is the spectral parameter, not the determinant exponent.

The actual lower functions are exactly

```text
K = TwoBlockDominantRectangular.quotientKernel
      ν.val ellu f Wtest.val hr 0
Nprofile = TwoBlockDominantRectangular.quotientNormProfile
      ν.val ellu f Wtest.val hr 0
Fiber = TwoBlockDominantRectangular.quotientFiberIntegrable
      ν.val ellu f Wtest.val hr 0.
```

Their rectangle measure is exactly
`(rectangularMeasure ν.val a k).prod (rectangularMeasure ν.val j b)`.
At a representative `g`, `K` integrates the actual raw five-block kernel
over `x : Matrix (Fin a) (Fin k) F.Carrier` and
`y : Matrix (Fin j) (Fin b) F.Carrier`. Its determinant exponent at zero is
`-(j+k+1)/2+j`, as in Section 4.10(2).
`Nprofile` integrates the norm of the raw weighted kernel, rather than
taking the norm after integration. `Fiber` asserts actual integrability of
that same rectangle integrand. The descended functions use simultaneous
rectangle covariance and exact supplied-Haar transport; the kernel at fixed
rectangles is not asserted to be invariant.

Independently of any epsilon certificate the statement asserts
`Measurable A` and `Measurable K`. For every integer `a` it asserts:

1. Product-space integrability of
   `(q,x) ↦ unequalRankIntegrand ψ abv j k Wup Wjac 0 x q`
   under `(νN.restrict (RankinSelberg.determinantSlice T t a)).prod μrect`.
2. Integrability of `K` under `νMinus` restricted to
   `TwoBlockLowerUnipotentQuotient.determinantSlice F h a`.
3. Integrability of `Nprofile` under this same restricted lower measure.
4. Almost-everywhere `Fiber` under this same restricted lower measure.

These are explicit analytic conclusions. No convergence is inferred from
an equality of totalized Bochner integrals. The lower conditions are
spelled out directly, rather than replacing them by a predicate about an
unrestricted outer measure. The statement requires no integration over the
entire outer quotient at spectral parameter zero.

## Common small-block witnesses and the Laurent identity

Separately, for every fixed `cε : ℂˣ`, `d : ℤ` and supplied certificate

```text
UnequalRankEpsilonEquation hlt q ψ abv νA ν.val
  π (σu 0) lambda (ellu 0) cε d,
```

the conclusion chooses common `ζ : ℂˣ` and `P Pdual : Polynomial ℂ` before
all sections, test coefficients and complementary rectangles. It retains
`HasModelMinusOneScalar (σu 0) (ellu 0) ζ` and the entire body of the
certificate with those same witnesses. For every `jsmall,ksmall` with
`hrsmall : r=m 0+(jsmall+ksmall+1)`, both actual normalized-generator
conditions hold, and every actual pair of coefficients in the two supplied
models has rational continuations `R,Rdual` satisfying both
`HasRationalContinuation` predicates and
`NormalizedFunctionalEquation q P Pdual ζ cε r d R Rdual`.

Here `IsNormalizedGenerator values P` requires `P.coeff 0 = 1` and equality
of the actual Laurent-coefficient span of rational values with the module
spanned by `1/P`. Thus `P,Pdual` are the actual normalized generators, not
arbitrary denominator clearers. Rational continuation includes agreement on
a right half-plane with the rational denominator nonzero there.

For each large complementary pair, the first-block calculation uses

```text
jsmall = (m 1+1)+j = b+j,    ksmall = k
r = m 0+(jsmall+ksmall+1).
```

Indeed `h` gives `t=m 0+m 1+1`, and substitution in `hr` proves the displayed
rank identity. The `b` Jacquet rows combine with the external `j` rows.
Keeping the complementary `k` rows in the five-block matrix gives the two
rectangles `a×k` and `j×b` after the same first-block calculation. This
explains the extension of the source's `k=0` illustration. The full
small-block witness body includes `jsmall=b+j,ksmall=k`; its universal
quantifiers do not specialize the parent to one block. The necessary
analytic disintegration, changes of variables and coefficient comparison
remain proof obligations.

For every `j,k,hr,f,Wtest`, define the bilateral coefficient function

```text
Zlow a = ∫ z, K z
  ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a).
```

With exactly the same `ζ,P,Pdual`, the final conjunct states

```text
D • Zlow =
  (LaurentPolynomial.C ((ζ : ℂ)^r * (cε : ℂ)) *
    LaurentPolynomial.T d * P.toLaurent) • Zup

D = Polynomial.eval₂ LaurentPolynomial.C
  (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) Pdual.
```

Thus `D` is precisely `Pdual(q⁻¹ X⁻¹)`, evaluated into Laurent polynomials.
The action is the published finite convolution on
`BilateralLaurentSeries = ℤ → ℂ`:
`(Q • Z)(a) = ∑ i ∈ Q.coeff.support, Q.coeff i * Z(a-i)`.
Both polynomial factors remain present. No rational action on arbitrary
bilateral coefficient functions or cancellation of a polynomial is used.

The source's sign is the first block's minus-one scalar raised to the
actual test rank minus one, hence to `r` in Lean. Its equation (2) has the
orientation

```text
(C(cε) * T(d) * P.toLaurent) • Zup = (C(ζ^r) * D) • Zlow.
```

The normalized-generator certificate forces a nonzero small coefficient
model: a zero model supplies only zero rational values and cannot generate
the nonzero module spanned by `1/P`. Apply the actual model minus-one
operation twice to a nonzero coefficient value. Since `(-I)^2=I`, this gives
`ζ²=1`. Multiplying the source equation by `ζ^r` yields the orientation
stated in Lean, without any polynomial cancellation. This uses the scalar
on the actual model and does not assume a central character on a reducible
original carrier.

Zero functionals, sections and coefficients remain in the convergence
clauses. A zero test functional or first-block functional gives a zero
small value set, which cannot have the required normalized generator; the
statement does not assert existence of a certificate in that case. If only
the second block functional vanishes, the large contractions and both large
coefficients vanish, while the conditional identity still retains any
supplied small certificate. Size-one blocks, `j=0` and `k=0` remain present.
The bilateral module can have polynomial torsion, so even a common
polynomial factor cannot be cancelled by this statement.

## Scope

This module supplies no analytic proof, factor existence, parameter
continuation, Section 4.10(3) reversed-dual comparison, rectangle Jacobian
comparison, or final gamma/L conclusion. The separately owned equal-total-rank
identity with a Schwartz row test is unchanged. This statement has no
Schwartz row test and uses no later multiplicativity.
