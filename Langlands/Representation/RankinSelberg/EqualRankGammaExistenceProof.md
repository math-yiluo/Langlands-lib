# Equal-rank JPSS gamma-factor existence

Author: Worker 364. The valuative-topology instance proof and its binder
pattern come from Worker 11's `FunctionalEquationStatement` as used in
Worker 358's `EqualRankGammaExistenceStatement`. This module reuses the
latter's shared `equalRankGamma_valuative_nonarchimedean` theorem, whose
original proof is unchanged.

`Langlands.RankinSelberg.equalRankGammaExistence` proves exactly
`Langlands.RankinSelberg.EqualRankGammaExistenceStatement.{uF,uV,uW} F T n`.
The field and two representation-carrier universes remain independent.
The theorem covers every prime, p-adic field, supplied topological data,
and positive rank `n+1`, including rank one. It retains every unitary
additive character, right-invariant unipotent Haar instance, compatible
quotient measure, supplied self-dual scalar Haar measure, possibly
reducible Whittaker-type pair and specified nonzero functional pair in
the target.

For those data it constructs one rational function `G` before all
coefficient vectors and Schwartz–Bruhat tests. The conclusion includes
the second model's minus-one scalar, a nonzero original rational value,
the actual plus-sign row Fourier partner for each test, and the original
and dual rational continuations with `GammaFunctionalEquation` on its
entire published denominator domain. The proof adds no hypothesis and
preserves the target. Integration exposes the target module's existing
instance theorem for reuse and removes its duplicate from this proof.

## Implemented proof

The main theorem first obtains the proved
`equalRankAnalytic.{uF,uV,uW} F T n`. It installs the topology, valuative
relation, local-field structure and Borel instances from the target.
The supplied Hausdorff structure `T.fieldT2`, additive uniform structure
and valuative basis of open submodules give the topological instances
needed by the row Fourier theorem. No different topology or measure is
chosen.

After introducing the target data, the proof applies `equalRankAnalytic`
twice. The first application gives the analytic conclusion for the
original pair. The second uses the inverse-transpose representations,
character `ψ.scale (-1)` and the actual first and second dual functionals.
The published `isOfWhittakerType_firstDual` and
`isOfWhittakerType_secondDual` provide their Whittaker-type hypotheses;
`firstDualFunctional_ne_zero` and `secondDualFunctional_ne_zero` preserve
the specified nonvanishing. Both applications retain the supplied
quotient measure and normalized absolute value.

The analytic conclusions supply normalized polynomials `P` and `Pd`.
`dualEqualRankRationalValues_eq` identifies the second value set with
the required dual rational values. The closure projection of
`Langlands.HarmonicAnalysis.rowFourierCompatibility ψ ν (n+1) hν`
supplies `RowFourierClosed` for the supplied self-dual measure `ν`.

`equalRankContinuedForms` then constructs two genuine trilinear families
`B s` and `Bd s` on the original coefficient models and row test space.
They have the same determinant-twisted invariance for every parameter.
Their separately guarded regular-point formulas are

```text
B s(f,f',Φ)  = P(q^(-s)) R(q^(-s))
Bd s(f,f',Φ) = Pd(q^(-(1-s))) Rd(q^(-(1-s))),
```

where `Rd` continues the actual dual integral of the Fourier partner.
The imported construction uses Laurent evaluation after denominator
clearing, so the forms remain defined at every parameter, including
poles of individual continuations.

`equalRankTrilinearUniqueness` supplies a finite exceptional spectral
set for these actual models. Its application to the invariant forms
shows that `Bd s` is a scalar multiple of `B s` whenever `B s ≠ 0` and
`q^(-s)` is outside that set. The final call to
`EqualRankGammaReduction.gammaEquation_of_continuedForms` uses this
proportionality and the evaluation formulas. The helper module, submitted
with this proof, has the following implemented algebra:

1. If `B s = 0`, both sides of the cross identity vanish. Otherwise
   proportionality proves the cross identity for every two test triples.
2. Remove the roots of `P` and the reflected roots of `Pd`, in addition
   to the uniqueness theorem's finite set. At regular points outside
   this union, cancel the two nonzero normalizing values.
3. The published spectral-to-rational comparison gives
   `subst δ (Rd i) * R j = subst δ (Rd j) * R i` as rational functions,
   where `δ = q⁻¹` and indices are model/test triples.
4. The normalized generator supplies a nonzero original member. Uniqueness
   of continuation identifies it with the selected original family.
   `exists_modelMinusOneScalar` gives a unit `ζ` acting on the second
   coefficient image, including the supplied `ℓ'`.
5. For a fixed nonzero original member indexed by `i₀`, set
   `G = subst δ (Rd i₀) / (C(ζ^n) * R i₀)` using `gammaRatio`.
   The rational cross identities yield
   `subst δ (Rd i) = C(ζ^n) * (G * R i)` for every triple.
   `gammaFunctionalEquation_of_rational_identity` gives the required
   equation on the full three-denominator domain.

The helper chooses the actual Fourier partners and both continuations
and packages these witnesses with `ζ` and the nonzero original value.
It requires neither a nonzero dual anchor nor Fourier surjectivity.
The target asserts existence of a rational `G`; this proof does not
separately assert that `G` is nonzero. The scope is exactly the existing
`EqualRankGammaEquation`.

## Original source and derived conventions

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.391, 395 and 396 (one-based PDF pages 26, 30 and 31) were read
visually during this task. No source erratum note was found in the
checked project, workspace or Library errata locations.

Theorem 2.7(ii), printed p.391, gives the rational continuations and
normalized reciprocal-polynomial generators. Section 2.10, p.396,
uses the matching right-translation identities (2.10.2)–(2.10.3) and
uniqueness of twisted invariant trilinear forms outside finitely many
values of `q^(-s)` to compare the original and Fourier-transformed dual
integrals. The implementation follows that route through the proved
analytic, Fourier, continued-form and uniqueness theorems. The finite
root exclusions, cross identities and explicit rational quotient are
the internal algebra used to finish the argument.

In the scan, (2.10.3) prints `1-s` on the left and appears to print `s`
in the right-hand dual integral. The Fourier change-of-variables
calculation gives matching twists at the same reflected dual parameter
`1-s` on both sides. As in the continued-forms statement and proof, the
implementation continues the actual dual integral in its own variable
`t` and evaluates it at `t=1-s`. This is a derived interpretation of the
display, not a claim about its printed text. The actual Fourier pairing
is the single plus-sign transform specified by the target.

Theorem 2.7(iii), p.391, expresses the normalized equation using the
second representation's sign `ω_σ(-1)^(r-1)`. Here `r=n+1`; the exponent
is `n` and the sign is implemented on the second coefficient image by
`ζ`. The rational comparison proved here is the intermediate gamma
existence conclusion. Epsilon normalization and existence are separate
results; neither is used as a premise of this proof.
