# Proof of the abstract simple twisted trace formula

Module `Langlands.TraceFormula.AbstractSimpleTwistedProof`, namespace `Langlands.TraceFormula`.

`abstractSimpleTwistedTraceFormula` proves `AbstractSimpleTwistedTraceFormulaStatement` (module
`Langlands.TraceFormula.AbstractSimpleTwistedStatement`, whose page describes its data and
hypotheses) at its full universe, with no added hypothesis.

## Statement

- `abstractSimpleTwistedTraceFormula : AbstractSimpleTwistedTraceFormulaStatement.{u}`.

  For the data and hypotheses of the statement, the conclusion is

  ```
  operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
    (twistOperator Γ θ hθΓ ν hθν)) =
    ∑ i, ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f
  ```

  that is, `tr(R(f) ∘ I_θ) = Σ_i vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`.

## Proof

`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` (module
`Langlands.TraceFormula.TwistedGeometricSide`) derives the statement from
`AbstractTwistedKernelDiagonalTraceStatement`, which `abstractTwistedKernelDiagonalTrace` (module
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`) proves. The first gives the
geometric side, `∫_{Γ \ G} K(x, x) dν = Σ_i vol · TO`. The second gives the analytic side,
`tr(R(f) ∘ I_θ) = ∫_{Γ \ G} K(x, x) dν`, from Brislawn's theorem.

Three hypotheses of the statement are not used by this proof:

- `MeasurePreserving θ μG μG`: neither half uses it. The analytic half uses only that `θ̄⁻¹`
  preserves `ν`.
- `∀ i, (μC i).IsOpenPosMeasure`.
- `∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (νC i)`: the geometric side proves it.

The right invariance `[μG.IsMulRightInvariant]` is used only by the geometric side, to obtain
compatible measures on `(Γ ∩ C_{r i}) \ G`. The analytic half does not use it.

## Declarations, in order

- `abstractSimpleTwistedTraceFormula`

## Literature

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), §18.5,
  Corollary 18.5.1, printed p. 488, the simple twisted trace formula (18.36). On the same page the
  trace of the trace class operator (18.34) is computed as the integral of the diagonal by
  [Bri91, Corollary 3.2]. The book's formula is for cuspidal spectra of reductive groups over number
  fields. The statement proved here is the general geometric identity described on the statement's
  page.
- C. Brislawn, *Traceable integral kernels on countably generated measure spaces*, Pacific J. Math.
  150 (1991), Corollary 3.2, printed p. 237.
