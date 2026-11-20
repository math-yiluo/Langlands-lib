# The factorization over S and the infinite places from the two pointwise premises

Task 7397 asks for `ArchimedeanFactorizationStatement`, the factorization of the partial
Rankin–Selberg Whittaker integrals over `S` and the infinite places, for both ranks (Cogdell
2004, proof of Theorem 4.1, pp.219-220). This module reduces that target to the two remaining
representation-theoretic premises.

## Statement

```
def ArchimedeanFactorizationFromPointwiseStatement : Prop :=
  UnequalPointwiseFactorizationStatement.{u, uQ} →
    EqualPointwiseFactorizationStatement.{u, uQ} → ArchimedeanFactorizationStatement.{u, uQ}
```

Both premises are published statements, and both are retained in full as hypotheses.

- `UnequalPointwiseFactorizationStatement` (module `ArchimedeanFactorizationReduction`,
  premise A_U). Take the target's unequal-rank data, with ranks `t < r`, the canonical finite
  characters `ψv v` and self-dual measures `νv v`. The premise asserts the following
  objects: vectors `x`, `x'` spherical outside `S`; a constant `κ ≠ 0`; functions `WR v`,
  `WR' v`, `WC w`, `WC' w` satisfying `IsRealPlaceWhittaker` or `IsComplexPlaceWhittaker` for
  `ψ.complex` and its inverse; real and complex quotient measure data; finite local test data
  `D v : PadicUnequalTestData` of the local components at the places `v` of `S`; and local
  integrands `fS v`, `gS v`. These satisfy:
  - for every `v ∈ S` and every `s`, with the quotient measure of `D v`, the quotient
    integral of `fS v s` is `(D v).integral h (νv v) s`, and the integral of `gS v s` over
    the quotient times the rectangle block (with `νv v`) is `(D v).dualIntegral h (νv v) s`;
  - for every spectral parameter `s` and every class `q` in `unipotentIntegralClasses`, the
    global integrand `unequalWhittakerIntegrand` at `s` and `q` is `κ` times the product of
    the real, complex and finite local integrands at the projections of `q`;
  - for every `s`, every such class `q` and every rectangular coordinate `y` (any adelic
    matrix of size `(r - (t + 1)) × (t + 1)`), the global dual kernel `dualWhittakerKernel` at
    `s`, `q`, `y` is `κ` times the value at `y` of the indicator of
    `rectIntegralOutside (r - (t + 1)) (t + 1) S` applied to the product of the real, complex
    and finite local dual kernels at the projections of `q` and `y`. Here
    `rectIntegralOutside` is the set of matrices whose entries are integral at every finite
    place outside `S`. In particular the dual kernel is zero for every `y` outside that set;
  - the product over the infinite places of the ordinary local integrals, and that of the
    dual local integrals, are nonzero at points arbitrarily far to the right, and so are
    each `(D v).integral h (νv v)` and `(D v).dualIntegral h (νv v)`.
- `EqualPointwiseFactorizationStatement` (module `EqualArchimedeanFactorizationReduction`,
  premise A_E). The equal-rank analogue, with finite test data `D v : EqualLocalTestData`
  and a global Schwartz–Bruhat function `Φ` standard outside `S`. `Φ` equals the indicator of
  the rows integral outside `S` times the product of archimedean Schwartz functions and of
  the finite tests `(D v).Φ`. Its Fourier transform is the same indicator times the product
  of the archimedean Fourier transforms and of the partners `(D v).Φhat`. On
  `unipotentIntegralClasses`, the equal-rank integrand of the global Whittaker functions
  with `Φ` and that of the dual Whittaker functions with the Fourier transform are both `κ`
  times products of local integrands, with the same `κ ≠ 0` and no rectangle. For each
  `v ∈ S`, the integrals of `fS v s` and `gS v s` over the quotient, for the measure
  `equalPadicQuotientMeasure`, are `(D v).integral s` and `(D v).dualIntegral s`. The four
  nonvanishing clauses have the same form as for A_U.

### Finite local existence in the Library

For both ranks the published local theory gives finite test data whose ordinary and dual
integrals are nonzero arbitrarily far to the right. Let `ψ` be a nontrivial additive
character of a p-adic field and `ν` a self-dual Haar measure for it. Let `π`, `σ` be
representations of Whittaker type for the standard character and its inverse, with given
nonzero Whittaker functionals `ℓ`, `ℓ'`.

- Equal rank. The theorem `EqualNonvanishing.padicEqualNonvanishingTest` (statement
  `PadicEqualNonvanishingTestStatement`, module `PadicEqualNonvanishingTests`) gives
  `EqualLocalTestData` with the functionals `ℓ`, `ℓ'` and the measure `ν`, with ordinary and
  dual integrals nonzero at points arbitrarily far to the right. Its proof uses the
  equal-rank unit-value theorem `equalRankUnitValue` (module `EqualRankUnitValueProof`) and
  the local functional equation. The statement module `EqualRankUnitValueStatement` cites
  the equal-rank test construction of Jacquet, Piatetski-Shapiro and Shalika 1983, printed
  p. 393.
- Unequal rank (`t < r`). The Library has no standalone theorem of this form for
  `PadicUnequalTestData`, but the same conclusion follows from published results. Apply
  `unequalRankFunctionalEquation` (JPSS 1983, Theorem 2.7(iii); module
  `UnequalRankFunctionalEquationProof`) with the compatible quotient measure
  `unipotentQuotientHaar` and with `ν`. It gives a normalized generator for the rational
  continuations of the block-zero (`j = 0`) integrals of all pairs of coefficient vectors.
  By `IsNormalizedGenerator.exists_ne_zero` (module `EpsilonFactor`) some pair has a
  nonzero continuation. For that same pair the normalized functional equation forces the
  continuation of the transformed integral to be nonzero
  (`EqualNonvanishing.dual_ne_zero_of_normalized`). By
  `EqualNonvanishing.nonvanishing_on_right_of_rational` each nonzero continuation gives
  nonzero values arbitrarily far to the right. The functionals `ℓ`, `ℓ'`, the quotient
  measure and this pair form `PadicUnequalTestData` whose `integral h ν` and
  `dualIntegral h ν` are nonzero at points arbitrarily far to the right. This module does
  not formalize the derivation.

Applying either result at a place of `S` needs the local components of the two cuspidal
representations to satisfy these Whittaker-type hypotheses for `ψv v` and its inverse,
with nonzero functionals.

### What the premises still retain

Both A_U and A_E retain, beyond this local existence:

- the globally compatible witnesses: the global vectors `x`, `x'` (and for equal rank `Φ`)
  must have global integrands and dual integrands that factor pointwise, with one `κ ≠ 0`,
  into local integrands whose local integrals are those of the chosen finite data `D v` of
  the local components at the places of `S`. The finite nonvanishing clauses are stated
  for these same data `D v`. The local results above supply suitable data at each place,
  but not their compatibility with the global choices;
- the archimedean nonvanishing clauses for the products of the real and complex local
  integrals, ordinary and dual.

For equal rank, the published theorem `equalPointwiseOfInfiniteTests` (module
`EqualInfiniteWhittakerReduction`) derives A_E from `EqualInfiniteWhittakerTestStatement`.
That statement retains the factorization of the normalized global residuals at the
infinite places and the archimedean nonvanishing. This module does not use that theorem: its
hypothesis is A_E itself.

## Proof

`archimedeanFactorizationFromPointwise` applies the published combined reduction
`archimedeanPointwiseFactorizationReduction` (module `EqualArchimedeanFactorizationReduction`,
statement `ArchimedeanPointwiseFactorizationReductionStatement`). That reduction proves
A_U → A_E → B → C → `ArchimedeanFactorizationStatement`. The theorem supplies the two
measure-theoretic premises from their proofs:

- premise B, `UnipotentClassProductStatement`, by
  `UnipotentClass.unipotentClassProductStatement` (module `UnipotentClassProductProof`);
- premise C, `RectangleTateStatement`, by `RectangleTate.rectangleTateStatement` (module
  `RectangleTateProof`).

The proof uses only the standard axioms.

## Provenance

Internal. The splitting of Cogdell's argument into the premises A_U, A_E, B, C is that of the
published reductions `ArchimedeanFactorizationReduction` (Worker 394) and
`EqualArchimedeanFactorizationReduction` (Worker 261). This module only composes them with the
proofs of B and C.
