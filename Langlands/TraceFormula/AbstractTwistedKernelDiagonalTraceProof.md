# Proof of the trace of `R(f) ∘ I_θ` as the integral of the diagonal of its kernel

Module `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`, namespace
`Langlands.TraceFormula`.

`abstractTwistedKernelDiagonalTrace` proves `AbstractTwistedKernelDiagonalTraceStatement` (module
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement`) at its full universe, with
no added hypothesis. It does not assume that `Γ \ G` is compact.

## Statements

- `integrable_twistedKernelDiagonal_and_operatorTrace_eq`: for `G : Type u` a group with
  `[TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]`, `μG : Measure G` with
  `[μG.IsHaarMeasure]`, `Γ : Subgroup G` with `[DiscreteTopology Γ]`,
  `[MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]`,
  `ν : Measure (LeftQuotient Γ)`, `hν : IsCompatible Γ μG Measure.count ν`, `θ : G ≃ₜ* G`,
  `hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ`,
  `hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν`,
  `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)`, `hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖`,
  `hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG`,
  `hπ : ∀ (g : G) (φ : Lp ℂ 2 ν), (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q)`,
  `f : C_c(G, ℂ)` and

  `htc : IsTraceClass ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
    (twistOperator Γ θ hθΓ ν hθν))`,

  the conclusion is

  ```
  Integrable (twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)) ν ∧
    operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) =
      ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν
  ```

  These are the data of `AbstractTwistedKernelDiagonalTraceStatement` without its hypotheses
  `[μG.IsMulRightInvariant]` and `MeasurePreserving θ μG μG`, which are not needed. The conclusion
  adds the integrability of the diagonal.

- `abstractTwistedKernelDiagonalTrace : AbstractTwistedKernelDiagonalTraceStatement.{u}`.

## Proof

Let `K = twistedQuotientKernel Γ θ _ f` (module `Langlands.TraceFormula.TwistedKernelOperator`) and
`T = R(f) ∘ I_θ`. Brislawn's theorem in the Library's form, `traceClassContinuousKernelDiagonal`
(module `Langlands.Analysis.TraceClassKernelDiagonalProof`), is applied with `X = Γ \ G` and the
measure `ν`. Its hypotheses are supplied as follows.

- `Γ \ G` is second countable (`TopologicalSpace.Quotient.secondCountableTopology` for the open map
  `π̄`). `ν` is σ-finite: it is regular (`IsCompatible.regular`), hence finite on compact sets, and
  `Γ \ G` is locally compact (`leftQuotient_locallyCompactSpace`) and second countable, hence
  σ-compact.
- `T` is trace class: `htc`.
- `K ∈ L²(ν × ν)`: `memLp_uncurry_twistedQuotientKernel`.
- `T φ =ᵐ (q ↦ ∫ K(q, q') φ(q') dν(q'))` for every `φ`: `twistedKernelOperator_ae_eq`.
- `K` is continuous at every diagonal point: `continuous_uncurry_twistedQuotientKernel`.

The theorem gives that `q ↦ K(q, q)` is integrable and `operatorTrace T = ∫ K(q, q) dν(q)`. By
`twistedQuotientKernel_self`, `q ↦ K(q, q)` is `twistedKernelDiagonal Γ θ _ f`. The statement is
the second half, after introducing its hypotheses (the unused `MeasurePreserving θ μG μG` among
them).

## Declarations, in order

- `integrable_twistedKernelDiagonal_and_operatorTrace_eq`
- `abstractTwistedKernelDiagonalTrace`

## Literature

- C. Brislawn, *Traceable integral kernels on countably generated measure spaces*, Pacific J. Math.
  150 (1991), 229–240, Corollary 3.2, printed p. 237: for a σ-finite Borel measure on a
  second-countable space and a trace class operator `K` on `L²(X, μ)` whose kernel `K(x, y)` is
  continuous at `(x, x)` for almost every `x`, `tr K = ∫ K(x, x) dμ(x)`. "The kernel" is the
  `L²(X × X)` kernel of (1.3), printed p. 230, as in §3, printed p. 235. Brislawn deduces the
  corollary from Theorem 3.1, printed p. 235, whose proof (pp. 235–237) also gives integrability of
  the averaged diagonal.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), §18.5, printed
  p. 487 (the kernel `K_f(g, θ(h))` of `R(f) ∘ I_θ`) and printed p. 488 (the trace of (18.34) as
  `∫_{[G]} K_{π(f)}(g, θ(g)) dg`, by [Bri91, Corollary 3.2]).
