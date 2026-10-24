# Analytic consequences for the compact root average

`Langlands.RankinSelberg.EqualRankRootAverageAnalyticStatement F T n` is an
internal conditional proposition for each supplied p-adic field and topology
in matrix rank `n + 1`, including rank one. The representation spaces have
independent universes. Its first premise is the full
`FiniteFunctionMellinStatement` at the field universe. For each pair of smooth
representations and character, it also assumes the standard- and
inverse-character `CoefficientTorusExpansion` propositions.

Write `A = (Fˣ)^(n+1)`, equipped with the product of the normalized
`localMultiplicativeHaar` measures. Let `κ` be the actual
`generalLinearHaar` restricted to the integral general linear subgroup. Put

```text
d(a)_i = ∏_{j ≥ i} a_j,
w(a) = (∏ i, (T.normalizedAbs(a_i) : ℂ)^((i+1)(n-i)))⁻¹,
H(f,f',Φ,s,a,z) = equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
                   (diagonalUnits(d(a)) * z) * w(a),
B(f,f',Φ,s,a) = ∫ H(f,f',Φ,s,a,z) dκ(z),
J(f,f',Φ,s) = ∫ B(f,f',Φ,s,a) dA(a).
```

The powers in `w` are natural powers. The spectral complex powers remain
inside the actual `equalRankFunction`. All integrals above are the existing
Bochner integrals, with no independently chosen scalar family.

There is a single nonzero Laurent polynomial `d`, chosen before both
Whittaker functionals. For every pair of functionals, including zero
functionals, the following hold for all actual coefficient-model vectors
`f,f'` and full-coordinate Schwartz row tests `Φ`:

- On a right half-plane depending on the test data, `B` is integrable over
  `A`, and the iterated nonnegative integral `∫⁻ a, ∫⁻ z, ‖H‖ₑ` is finite.
- The function `J` has a rational continuation in
  `q^(-s)`, for `q = T.residueCardinality`, in the precise
  `HasRationalContinuation` sense, including reduced-denominator nonvanishing.
- Every rational continuation `R` of `J` is cleared by this same `d`: there
  exists a Laurent polynomial `P` with
  `laurentToRatFunc P = laurentToRatFunc d * R`.

The denominator is independent of the functionals, coefficient vectors and
Schwartz test. The convergence bounds and individual rational functions may
depend on these data. No nonzero functional condition is imposed.

This is an internal composition of the published
`EqualRankCompactRootExpansionStatement` and
`FiniteFunctionMellinStatement`, together with finite linear continuation
and fixed-denominator closure. The compact expansion chooses its finite
translation-finite family before all test data. Applying the Mellin premise
to the finite set of these functions gives a denominator uniform over every
Schwartz coefficient. Finitely many convergence half-planes can be
intersected, finite sums are integrable, and the compact absolute-average
formula gives a finite sum of integrable norms. Finite linear continuation
then gives a continuation of `J`; uniqueness for the residue cardinality
greater than one gives the denominator assertion for every continuation.
This paragraph describes the derivation and intended proof obligations;
this module supplies only the proposition definition.

The proposition does not yet assert integrability on the product measure
or the quotient, identify `J` with the actual quotient integral, or establish
a normalized generator. Those steps require the measurability, quotient
Iwasawa and root-coordinate change-of-variables arguments and the separate
unit-value algebra. It adds no independent attribution to original literature.
