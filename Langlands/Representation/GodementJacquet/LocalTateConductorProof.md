# Proof of scalar Tate theory with its principal-unit conductor

`Langlands.GodementJacquet.localTateConductor` proves
`Langlands.GodementJacquet.LocalTateConductorStatement.{uF}` for an unrestricted
field universe. The statement and its sources are described in
`LocalTateConductorStatement.md`, which this proof leaves unchanged. The proof
works over an arbitrary nonarchimedean local field, including positive
characteristic. It uses the actual scalar Mellin integrals against
`localMultiplicativeHaar F` and the actual plus-sign Fourier integral. The
conductor, the analytic data, the normalized generators and the functional
equation are all derived; none of them is assumed.

The supporting development is in seven helper modules, each with its own
Markdown:

- `LocalTateLattice`: orders, lattices `ϖ^n O`, coset indicators, and
  induction over Schwartz--Bruhat functions.
- `LocalTateFourier`: additive orthogonality, Fourier integrals of coset
  indicators, and dilation.
- `LocalTateUnits`: principal-unit levels and the identification of the
  target's matrix levels with them.
- `LocalTateHaar`: comparison of multiplicative and additive Haar measure on
  `O^×`, and unit and Gauss integrals of characters.
- `LocalTateMellin`: the shell expansion of the Mellin integral.
- `LocalTateLaurent`: Laurent numerators, the Euler polynomial and rational
  continuation.
- `LocalTateFunctionalEquation`: the Laurent-level functional equation for
  the base indicators, and its closure properties.

## Reduction to a normalization

The final theorem introduces the target's binders and packages
`q, hq, abv, ϖ, hϖ, habvϖ, habv1` into a `LocalTate.Normalization F`. It then
applies `localTateConductor_of_normalization`, whose conclusion is the target's
conclusion verbatim.

## The conductor

`a` is the published `characterConductor F χ hχc`.
`characterConductor_spec` (from `LocalTateConductorPreliminaries`) gives
exactly the two matrix-level clauses of the target. `isUnitConductor_iff`
converts them to `IsUnitConductor χ a`: `χ` is trivial on `1 + ϖ^a O` (on
`O^×` if `a = 0`) and nontrivial at every smaller level index `b < a`
(equivalently, on every corresponding larger subgroup). `IsUnitConductor.inv`
gives the same for `χ⁻¹`. The target's dual character
`x ↦ ((χ x)⁻¹ : ℂ)` is rewritten as `x ↦ ((χ⁻¹ x : ℂˣ) : ℂ)`.

## Analytic data and generators

For `η ∈ {χ, χ⁻¹}` with conductor `a`, let `P_η = eulerPoly η a`. This is
literally the target's `P` (for `χ`) and `PDual` (for `χ⁻¹`).

- `scalarMellinAnalyticData_of_isUnitConductor` proves all three components.
  Convergence holds on the half-plane `Re s > log_q ‖η(ϖ)‖`
  (`integrable_mellinIntegrand`). Each test has the rational continuation
  `ℓ / P_η` (`exists_hasLaurentMellin`,
  `hasRationalContinuation_of_hasLaurentMellin`). The common denominator comes
  from the generator property below.
- `isNormalizedGenerator_eulerPoly` uses the published
  `isNormalizedGenerator_iff`. It needs three facts.
  - The constant coefficient of `P_η` is one.
  - Every rational value `R` satisfies `P_η R = ℓ`, which is a Laurent
    polynomial (`laurentToRatFunc_eq_of_hasLaurentMellin`, from uniqueness of
    rational continuation).
  - `P_η⁻¹` lies in the Laurent span of the values
    (`inv_eulerPoly_mem_zetaSpan`). If `a = 0`, the indicator `1_O` has
    numerator `1`. If `a ≥ 1`, the indicator of `1 + ϖ^a O` has numerator the
    nonzero constant `μ^×(1 + ϖ^a O) = ν(ϖ^a O)/ν({v = 1})`. In both cases a
    test value equals `κ P_η⁻¹` with `κ ≠ 0`.

## Functional equation

`feData_all` proves `FEData (feConstant)` for every Schwartz--Bruhat `Φ`. It
uses `schwartzBruhat_induction` with the closure lemmas `feData_zero`,
`feData_add` and `feData_smul`. For a coset `x0 + ϖ^n O` there are two cases:

- If `x0 ∈ ϖ^n O`, the indicator is a dilate of `1_O`
  (`feData_integer`, `feData_dilate`).
- Otherwise it is a dilate of `1_{1 + ϖ^m O}` with `m ≥ 1`
  (`feData_unitLevel`, `feData_dilate`).

`feConstant_ne_zero` shows that the constant is nonzero. If `a = 0`, it is
`ν(O) > 0`. If `a ≥ 1`, suppose the constant is zero. Let `Φ0` be the Fourier
witness of `1_{-1 + ϖ^a O}`. Self-duality of `ν` (`IsSelfDual`) shows that the
Fourier transform of `Φ0` is `1_{1 + ϖ^a O}`. `FEData` for `Φ0` then gives a
dual numerator `ℓ'` with `ℓ'(X_s) = 0` for all `s`, using
`dualUnit_dualUnit`. But the dual Mellin integral of `1_{1 + ϖ^a O}` equals
the positive volume `μ^×(1 + ϖ^a O)` on a right half-plane
(`hasLaurentMellin_unitLevel` for `χ⁻¹`). This is a contradiction.

The final step sets `c = feConstant` as a unit. Given `Φ`, take `Φhat` to be
the witness `Ψ` from `FEData`; integrability is the published
`fourierIntegrand_integrable`. For arbitrary continuations `R` and `RDual`,
uniqueness gives `ℓ = P R` and `ℓ' = PDual RDual` as rational functions. At an
`s` where both denominators are nonzero, the published
`laurentEval_eq_of_laurentToRatFunc_eq` evaluates them at `X_s` and at
`q⁻¹X_s⁻¹ = X_{1-s}`. The dual relation then reads

`PDual(X_{1-s}) RDual(X_{1-s}) = c · X_s^a · P(X_s) R(X_s)`.

This is `NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual`, because the
sign factor `1^0` is one.

## Route and provenance

The mathematics is Tate's local theory: Tate's thesis (source
`tate-1967-thesis`, §2.4--2.5) and the survey
`tate-1979-number-theoretic-background`, (3.1.3), (3.2.1) and (3.2.6). Both are
cited in the statement's Markdown. The implemented proof follows a different
route from Tate's `Z(Φ, Ψ^) = Z(Φ^, Ψ)` argument. It computes Laurent numerators
by an explicit shell expansion and verifies the functional equation on
lattice-coset indicators, which it reaches from `1_O` and `1_{1 + ϖ^m O}` by
dilation. It extends the equation by linearity, and it proves the epsilon
constant nonzero by the self-duality argument above. Every intermediate
definition (`Normalization`, `HasLaurentMellin`, `FEData`, `feConstant`,
`DualRelation`, `IsUnitConductor`) is an internal device of this proof.
