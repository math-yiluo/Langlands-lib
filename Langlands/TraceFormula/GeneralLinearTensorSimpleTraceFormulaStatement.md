# The simple trace formula for `GL_n` on sums of tensor test functions (statement)

`Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaStatement` contains three proposition
definitions and no proof, in the namespace `Langlands.TraceFormula`. Notation as on the page of
`GeneralLinearSimpleTraceFormulaStatement` (the module repeats its two local instances and the local
notation `GLₙ`).

## `GeneralLinearSimpleTraceExpansion`

`GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h`, for an integrable `f` on `GL_n(𝔸_F)`,
is the conclusion of `GeneralLinearSimpleTraceFormulaStatement` after its integrability clause,
copied without change: `R(f)` is trace class on `L²([G])`, and there are finitely many pairwise
non-conjugate rational norm-one points `r j`, regular elliptic at `v`, containing every class that
meets the support of `f¹`, such that for all compatible centralizer and quotient measures the volumes
are finite, the orbit functions of `f¹` are integrable, and
`tr R(f) = ∑ j, vol((Γ ∩ C j) \ C j) · O_{r j}(f¹)`.

## Hypotheses of the two tensor statements

With the parameters of the existing statement, `μG = Measure.haar` on `GL_n(𝔸_F)`, and functions on
`AdelicGL F n` read on `GL_n(𝔸_F)` through `GeneralLinearGroupPoints.adelicHomeomorph F n`:

- (1) every tensor test function `a ⊗ b` (`adelicTestTensor F n a b`, `a` a smooth compactly
  supported archimedean kernel, `b` a compactly supported locally constant finite test) has a
  Hilbert–Schmidt cuspidal operator;
- (2) for each `j`, the finite component `bⱼ` has vanishing integrals
  `∫ bⱼ(x · u(Z) · y) dν(Z) = 0` over the two-block unipotent subgroups `u(Z)` of `GL_n(F_{wⱼ})` at
  some finite place `wⱼ` (`FiniteAdelicGL.localInclusion`, `blockUnipotent`), for every Haar measure
  `ν` and all `x`, `y` in `GL_n(𝔸_f)`;
- (3) every point of the support of each `aⱼ ⊗ bⱼ` is regular elliptic at the finite place `v`.

Let `f = ∑ⱼ aⱼ ⊗ bⱼ` (`fun g => ∑ j, adelicTestTensor F n (a j) (b j) (adelicHomeomorph F n g)`).

## `GeneralLinearTensorSimpleTraceFormulaStatement`

Under (1)–(3), `f` is integrable and satisfies the simple trace formula at `v` with one family of
representatives:

`∃ h : Integrable f μG, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h`.

That is, `R(f)` is trace class, and there are finitely many pairwise non-conjugate rational
norm-one points `r j`, regular elliptic at `v` and meeting every class on which the orbit function of
`f¹` does not vanish, with `tr R(f) = ∑ j, vol((Γ ∩ C j) \ C j) · O_{r j}(f¹)` for all compatible
measures.

## `GeneralLinearTensorSimpleTracePiecesStatement`

Under (1)–(3), `f` is integrable, `R(f)` is trace class, and there are `N` and
`f₁ f₂ : Fin N → C_c(GL_n(𝔸_F), ℂ)` with `f = ∑ₖ f₁ₖ ⋆ f₂ₖ`, every piece `f₁ₖ ⋆ f₂ₖ` integrable and
satisfying `GeneralLinearSimpleTraceExpansion` at `v`, each with its own family of
representatives, and `tr R(f) = ∑ₖ tr R(f₁ₖ ⋆ f₂ₖ)`.

## How the two statements are related

The pieces statement is the form the existing statement gives directly: each convolution
`f₁ₖ ⋆ f₂ₖ` comes with a family of representatives that the existing statement does not specify. The
single-expansion statement follows from it by merging these families: a term
`vol((Γ ∩ C) \ C) · O_γ(f¹)` is the same for two representatives of one class and for all admissible
measures (`TwistedOrbitalTermInvariance`), the averages and orbital integrals are additive in the
function, and the pieces' expansions are merged class by class
(`SimpleTraceGeometricExpansionSum`, `GeneralLinearSimpleTraceExpansionMerge`). Both statements
are proved in `GeneralLinearTensorSimpleTraceFormulaReduction` from
`GeneralLinearSimpleTraceFormulaStatement` and `GeneralLinearRadicalIntegralVanishingStatement`.

## Source

Getz–Hahn 2024, Corollary 18.4.1, as cited on the page of `GeneralLinearSimpleTraceFormulaStatement`;
the factorization of tensor tests is `Langlands.TraceFormula.CompactSmoothAdelicGLTestConvolution`.
