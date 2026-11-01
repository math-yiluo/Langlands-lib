# Finite numerators for actual strictly dominant Jacquet coefficients

This internal specialization uses the actual unequal-rank determinant
coefficients, the actual reversed-dual section, and the published matrix
comparison. It does not assert a first-block functional equation.

`strictDualSliceCoefficient` applies `strictSliceCoefficient` with exchanged
complementary dimensions, the inverse additive character, the same supplied
quotient and scalar Haar measures, and `reversedDualTest`. The latter retains
the prescribed right factor `diag(I_(n+1),w_(j+k+1))`.

`strictDualSliceCoefficient_lowerSupport` uses
`translatedFirstDualModelEquiv` to place that test in the actual coefficient
model for `inverseTransposePullback π`. Smoothness of that representation
follows from `inverseTransposePullback_isSmooth`. The existing actual support
theorem then proves a finite negative tail for every smaller inverse-character
Whittaker function. No type or smoothness condition on the smaller function,
compatibility of measures, or convergence is required for this support result.

`strictResidueCardinalityUnit` is the canonical residue cardinality `qF`
regarded as a complex unit. Its nonzeroness follows from `qF > 1`.

`twoBlock_strictInducedCoefficient_numerators` specializes the existing
`twoBlock_cleared_numerators` to four actual coefficient series. Its data
retain the independent field, test-carrier and dependent block-carrier
universes. The original induced representation is
`TwoBlockJacquet.inducedRep F h σ`. The dual induced representation reverses
the entire family: sizes `m i.rev`, carriers `W i.rev`, and representations
`inverseTransposePullback (σ i.rev)`, using `reverse_sum h`.
The section is the actual fixed `reversedDualSectionEquiv F h σ hσ f`,
chosen before characters, tests, functionals and measures.

The original series `a` is the strict unequal-rank coefficient of `Wtest`
and the image of `f` under the supplied ordinary inverse-character
functional `J`. The dual series `aD` uses the same supplied standard
quotient measure and scalar Haar, the prescribed translated dual test,
and the image of the reversed section under the supplied ordinary
functional `JD`. These functionals are arbitrary in the theorem;
no identification with a convergent Jacquet integral is proved here.
The two other series `b,bD` are the actual lower-kernel slice coefficients
for `ell` and its completely reversed dual family, respectively.

For complex units `c₁,c₂`, integer exponents `d₁,d₂`, and polynomials
`P₁,P₁D,P₂,P₂D`, the two explicit premises are

```text
P₁D(qF⁻¹ X⁻¹) • b  = c₁ X^d₁ P₁(X) • a,
P₂(qF⁻¹ X⁻¹)  • bD = c₂ X^d₂ P₂D(X) • aD.
```

The published `twoBlockDominantDualMatrix` discharges the matrix premise
of `reversedDualSliceCoefficient_eq`. With the supplied standard measure's
compatibility and right invariance of the standard unipotent Haar, that
theorem gives `bD(-d)=qF^(-d)*b(d)`. The original lower-support theorem and
the translated dual support theorem discharge both support premises.
Applying `twoBlock_cleared_numerators` produces a unique finite Laurent
polynomial `R` with

```text
ofLaurentPolynomial R = (P₁ P₂) • a,
ofLaurentPolynomial (laurentReflection qF R)
  = [laurentReflection qF M⁻¹ * P₁D P₂D] • aD,
M = c₁ c₂⁻¹ qF^d₂ X^(d₁+d₂).
```

The multiplier is the existing proved Laurent unit
`clearedProductMultiplierUnit`. The implemented proof removes only that
unit and uses opposite one-sided support to extract a finite numerator;
it never cancels a general polynomial action on bilateral series.

This is an internal deduction from the imported support, actual dual-slice
transport, matrix proof and Laurent clearing results. It does not establish
the two first-block premises, absolute integrability of either Jacquet
realization, rational continuation, factor certificates, the equal-rank
boundary, or either final dominant gamma/L target. The two block equations
are the remaining analytic input to this particular numerator result.
