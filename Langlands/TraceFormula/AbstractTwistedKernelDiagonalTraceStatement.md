# The trace of `R(f) ∘ I_θ` as the integral of the diagonal of its kernel

`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement` is a proposition
definition, in the module `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement`. It
supplies no proof. The statement is proved by `abstractTwistedKernelDiagonalTrace` (module
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`).

It is the analytic half of the simple twisted trace formula: for a trace-class `R(f) ∘ I_θ` on
`L²(Γ \ G)`, its trace is the integral over `Γ \ G` of the diagonal `x ↦ K(x, x)` of the twisted
kernel `K(x, y) = Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y))`. The geometric half, from that integral to volumes times
twisted orbital integrals, is proved in `Langlands.TraceFormula.TwistedGeometricSide`; together they
give `AbstractSimpleTwistedTraceFormulaStatement`
(`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace`), which is proved by
`abstractSimpleTwistedTraceFormula` (module `Langlands.TraceFormula.AbstractSimpleTwistedProof`).

## Statement

The data and hypotheses are those of `AbstractSimpleTwistedTraceFormulaStatement` (module
`Langlands.TraceFormula.AbstractSimpleTwistedStatement`, whose page describes them) up to and
including its trace-class hypothesis:

- a group `G : Type uG`, a Hausdorff, locally compact, second-countable topological group with its
  Borel σ-algebra, and a measure `μG` that is a left Haar measure and right invariant;
- a subgroup `Γ` with `[DiscreteTopology Γ]`, a Borel σ-algebra on `LeftQuotient Γ` (the space
  `Γ \ G` of cosets `Γ g`) and a measure `ν` on it with `IsCompatible Γ μG Measure.count ν`;
- `θ : G ≃ₜ* G` with `hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ`, `MeasurePreserving θ μG μG`, and
  `hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν`;
- `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` with `hπnorm : ∀ g φ, ‖π g φ‖ = ‖φ‖`,
  `hπmeas : ∀ φ, AEStronglyMeasurable (fun g => π g φ) μG` and
  `∀ g φ, (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q)`;
- `f : C_c(G, ℂ)` such that
  `IsTraceClass ((integratedIsometricAction μG π hπnorm hπmeas f _).comp (twistOperator Γ θ hθΓ ν hθν))`.

The conclusion is

```
operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
  (twistOperator Γ θ hθΓ ν hθν)) =
  ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν
```

where `twistedKernelDiagonal Γ θ _ f` (module `Langlands.TraceFormula.TwistedOrbital`) is the
function `Γ x ↦ Σ' γ : Γ, f (x⁻¹ * γ * θ x)` on `Γ \ G`, and `∫` is the Bochner integral. The
support condition of `AbstractSimpleTwistedTraceFormulaStatement` (its hypothesis 2, placed after
the trace-class hypothesis) is not among the hypotheses: the identity does not need it. Two of the
hypotheses that are present are not needed either: the right invariance `[μG.IsMulRightInvariant]`
and `MeasurePreserving θ μG μG`. The Library proves the identity, together with the integrability
of the diagonal, without them (`integrable_twistedKernelDiagonal_and_operatorTrace_eq`, module
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`).

## The kernel, in the Library's conventions

Write `π̄` for the map `G → Γ \ G`, `x̄ = π̄(x)`, and `θ̄` for `quotientAutomorphism Γ θ hθΓ`,
the homeomorphism `Γ x ↦ Γ θ(x)` of `Γ \ G`; its inverse is `Γ x ↦ Γ θ⁻¹(x)`
(`quotientAutomorphism_symm_mk`).

- `rightTranslate Γ g` is `Γ x ↦ Γ (x g)`; so `(π(g) φ)(x̄) = φ(\overline{x g})` for `ν`-almost
  every `x̄`.
- `R(f) = integratedIsometricAction μG π … f …` is `ψ ↦ ∫_G f(g) π(g) ψ dμG(g)`
  (`integratedIsometricAction_apply`); so `(R(f) ψ)(x̄) = ∫_G f(g) ψ(\overline{x g}) dμG(g)` for
  almost every `x̄`.
- `I_θ = twistOperator Γ θ hθΓ ν hθν` is composition with `θ̄⁻¹` (`twistOperator_coeFn`):
  `(I_θ φ)(x̄) = φ(\overline{θ⁻¹(x)})`.
- `R(f) ∘ I_θ` is `(integratedIsometricAction …).comp (twistOperator …)`: first `I_θ`, then `R(f)`.

Hence, for `φ ∈ L²(Γ \ G)` and almost every `x̄`,

```
(R(f) I_θ φ)(x̄) = ∫_G f(g) φ(\overline{θ⁻¹(x g)}) dμG(g)
               = ∫_G f(x⁻¹ θ(y)) φ(ȳ) dμG(y)                          (g = x⁻¹ θ(y))
               = ∫_{Γ \ G} Σ_{γ ∈ Γ} f(x⁻¹ θ(γ y)) φ(ȳ) dν(ȳ)         (IsCompatible Γ μG count ν)
               = ∫_{Γ \ G} Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y)) φ(ȳ) dν(ȳ)         (θ(Γ) = Γ).
```

The substitution `g = x⁻¹ θ(y)` preserves `μG` because left translation by `x⁻¹` does (left Haar
measure) and `θ` does (`MeasurePreserving θ μG μG`); the third line is the compatibility formula of
`ν`, extended from compactly supported continuous functions by the module
`Langlands.Analysis.Local.QuotientNormalizingFunction`; the last line uses that `θ` maps `Γ` onto `Γ`
(`hθΓ` and bijectivity of `θ`). So `R(f) ∘ I_θ` is the integral operator with kernel
`K(x̄, ȳ) = Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y)) = twistedKernel Γ θ f x y`, which is left `Γ`-invariant in both
variables (`twistedKernel_left_mul_left`, `twistedKernel_left_mul_right`). Its diagonal is
`twistedKernelDiagonal Γ θ _ f`, with `θ` and not `θ⁻¹`. This agrees with Getz–Hahn's kernel
`K_f(g, θ(h))` of `R(f) ∘ I_θ` for `I_θ φ = φ ∘ θ⁻¹` (below).

## Why the statement holds

This section gives the argument from the literature; the Lean proof, in
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`, follows it (the Lean names are at
the end of the section).

**What Brislawn proves.** C. Brislawn, *Traceable integral kernels on countably generated measure
spaces* (1991), Corollary 3.2, printed p. 237: *let `μ` be a σ-finite Borel measure on a
second-countable space `X`, and let `K` be a trace class operator on `L²(X, μ)`; if the kernel
`K(x, y)` is continuous at `(x, x)` for almost every `x`, then `tr K = ∫ K(x, x) dμ(x)`.* "The
kernel" is the kernel of the Hilbert–Schmidt operator `K`, a function `K(x, y) ∈ L²(X × X, μ × μ)`
with `K f (x) = ∫_X K(x, y) f(y) dμ(y)` ((1.3), printed p. 230; the setting of §3, printed p. 235);
continuity is asked of this function, as a function on `X × X`, at the diagonal points. The corollary
does not state that `x ↦ K(x, x)` is integrable. That follows from Theorem 3.1 (printed p. 235: for
every trace class `K` the maximal function `M⁽²⁾K(x, x)` is integrable, the averaged diagonal
`K̃(x, x)` exists almost everywhere and `tr K = ∫ K̃(x, x) dμ(x)`), whose proof bounds `K̃(x, x)` by an
integrable series (printed pp. 236–237), together with Theorem 2.4 and (2.11) (printed p. 234: where
the kernel is continuous at `(x, x)`, `K̃(x, x) = K(x, x)`, for almost every `x`). The Library's
`Langlands.Analysis.OperatorIdeals.TraceClassContinuousKernelDiagonalStatement` (module
`Langlands.Analysis.TraceClassKernelDiagonalStatement`, not imported here) states the corollary
together with this integrability, for a kernel in `L²(X × X)` given by its integral formula on `Lp`.

**The hypotheses for `R(f) ∘ I_θ`.** Under the hypotheses of
`AbstractTwistedKernelDiagonalTraceStatement`:

- `X = Γ \ G` is second countable (the image of the second-countable `G` under an open map), and `ν`
  is a measure on its Borel σ-algebra (`BorelSpace`). It is σ-finite: it is finite on compact sets
  (`ν` is regular, a field of `IsCompatible`) and `Γ \ G` is locally compact and second countable,
  hence σ-compact.
- `R(f) ∘ I_θ` is trace class by hypothesis. Brislawn's trace class operators are those with
  absolutely summable singular values (printed p. 229), and his trace is the usual one, computed on
  printed p. 237 as `Σ (K ψ_i, ψ_i)` over the orthonormal family `ψ_i` spanning `ker(K)^⊥` ((1.1),
  p. 229); these are the Library's `IsTraceClass` and `operatorTrace`, which does not depend on the
  basis (`operatorTraceBasis`).
- The kernel. A trace class operator is Hilbert–Schmidt, so `R(f) ∘ I_θ` has a kernel in
  `L²(X × X)` ((1.3)). By the computation above it acts as the integral operator with kernel
  `K(x̄, ȳ) = Σ_γ f(x⁻¹ γ θ(y))`; this identity at the level of `Lp` (evaluating the Bochner integral
  that defines `R(f)` almost everywhere) is `twistedKernelOperator_ae_eq` (module
  `Langlands.TraceFormula.TwistedKernelOperator`), proved through `quotientL2Unfolding` and the
  invariance of `ν` under `θ̄⁻¹`. For each `x̄`, `K(x̄, ·)`
  is continuous and vanishes outside the image of the compact set `θ⁻¹(x · supp f)`, so it is
  square integrable; comparing the two kernels on a countable dense set of `φ` shows that the `L²`
  kernel equals `K` almost everywhere. So `K` is a representative of Brislawn's kernel, and
  `K ∈ L²(X × X)`.
- Continuity. `K` is continuous on `X × X`: on `G × G` it is locally a finite sum of continuous
  functions (only finitely many `γ` meet a compact set, `Γ` being discrete), and it descends along
  the open map `G × G → X × X`. So it is continuous at every diagonal point, not only at almost
  every one.

So Corollary 3.2 applies to `R(f) ∘ I_θ` with this kernel and gives
`tr(R(f) ∘ I_θ) = ∫ K(x̄, x̄) dν(x̄)`; by Theorem 3.1 and Theorem 2.4 the diagonal is integrable, so
this integral is the Bochner integral `∫ q, twistedKernelDiagonal Γ θ _ f q ∂ν` of the statement.
The support condition of `AbstractSimpleTwistedTraceFormulaStatement` is not used.

In Lean, `integrable_twistedKernelDiagonal_and_operatorTrace_eq` applies
`Langlands.Analysis.OperatorIdeals.traceClassContinuousKernelDiagonal` (module
`Langlands.Analysis.TraceClassKernelDiagonalProof`, which proves
`TraceClassContinuousKernelDiagonalStatement`) to the kernel `twistedQuotientKernel Γ θ _ f` on
`Γ \ G × Γ \ G` (module `Langlands.TraceFormula.TwistedKernelOperator`): the kernel is in
`L²(ν × ν)` (`memLp_uncurry_twistedQuotientKernel`), the operator is the integral operator with this
kernel (`twistedKernelOperator_ae_eq`), the kernel is continuous
(`continuous_uncurry_twistedQuotientKernel`), and its diagonal is `twistedKernelDiagonal Γ θ _ f`
(`twistedQuotientKernel_self`). `twistedKernelOperator_ae_eq` uses the invariance of `ν` under
`θ̄⁻¹` (`hθν`) in place of the substitution above, so neither `[μG.IsMulRightInvariant]` nor
`MeasurePreserving θ μG μG` enters the proof. `abstractTwistedKernelDiagonalTrace` is the second
half of its conclusion.

## Literature

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §18.5, printed p. 487:
  (18.33), `I_θ φ = (g ↦ φ(θ⁻¹(g)))`, and "the composite `R(f) ∘ I_θ` … has kernel function
  `K_f(g, θ(h))`"; printed p. 488: `∫_{[G]} K_{π(f)}(g, θ(g)) dg` is the trace of the trace class
  operator (18.34) "by [Bri91, Corollary 3.2]". The book works on `L²([G])`, `[G] = A_G G(F) \ G(𝔸_F)`,
  and on its cuspidal part; here `G`, `Γ`, `θ` and the measures are general.
- C. Brislawn, *Traceable integral kernels on countably generated measure spaces*, Pacific J. Math.
  150 (1991), 229–240: (1.3), printed p. 230; Theorem 2.4 and (2.11), printed p. 234; §3 and
  Theorem 3.1, printed p. 235, with its proof, pp. 235–237; Corollary 3.2, printed p. 237 (the result
  cited by Getz–Hahn on p. 488). On printed p. 231 Brislawn presents Corollary 3.2 as a new proof of
  Duflo's theorem for continuous trace class kernels (Duflo, Théorème V.3.1.1), without Duflo's
  assumptions that `X` be locally compact and σ-compact and `μ` a Radon measure.
