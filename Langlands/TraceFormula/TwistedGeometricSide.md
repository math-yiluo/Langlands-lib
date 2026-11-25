# The geometric side of the simple twisted trace formula

Module `Langlands.TraceFormula.TwistedGeometricSide`, namespace `Langlands.TraceFormula`.

The unfolding (`TwistedGeometricUnfolding`) writes the integral of the diagonal of the twisted kernel
as a sum of integrals over `(Γ ∩ C_{r i}) \ G`; quotients in stages (`QuotientInStages`) write each of
them as `vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`. This module puts the two together and states the
result in the forms consumed by the Library's statements on the geometric side:
`TwistedGeometricMeasures` and `SingleOrbitGeometricTraceStatement`
(`SingleOrbitGeometricTrace`), and `AbstractSimpleTwistedTraceFormulaStatement`
(`AbstractSimpleTwistedStatement`), which it reduces to `AbstractTwistedKernelDiagonalTraceStatement`
(`AbstractTwistedKernelDiagonalTraceStatement`).

Every coset space `LeftQuotient H` that does not come with its own measurable structure carries the
Borel σ-algebra `leftQuotientMeasurableSpace`, installed as a local instance, as in
`SingleOrbitGeometricTrace`.

## Statements

Common hypotheses (the data of `twistedGeometricSide_unfolding`): `G` a topological group,
Hausdorff, locally compact, second countable, with its Borel σ-algebra; `μG` with
`[μG.IsHaarMeasure] [μG.IsMulRightInvariant]`; `Γ` with `[DiscreteTopology Γ]`; measurable Borel
structure on `LeftQuotient Γ` and `hν : IsCompatible Γ μG Measure.count ν`; `θ` continuous with
`hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ`; `f : C_c(G, ℂ)`;
`hsupp : ∃ C : Set G, IsCompact C ∧ ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y`;
`r : ι → Γ` with `hr` (pairwise not `Γ`-`θ`-conjugate) and `hcover` (every `γ ∈ Γ` with
`∃ x, f (x⁻¹ * γ * θ x) ≠ 0` is conjugate to some `r i`).

- `hasSum_twistedOrbitalIntegral_of_isCompatible`, for `θ : Θ` with `[MonoidHomClass Θ G G]`,
  measures `μC i` on `twistedCentralizer θ (r i : G)` with
  `[∀ i, (μC i).IsMulRightInvariant] [∀ i, IsFiniteMeasureOnCompacts (μC i)]`,
  `hνC : ∀ i, IsCompatible (twistedCentralizer θ (r i : G)) μG (μC i) (νC i)`,
  `hνΓC : ∀ i, IsCompatible (Γ.subgroupOf (twistedCentralizer θ (r i : G))) (μC i) Measure.count (νΓC i)`,
  `hfin : ∀ i, νΓC i Set.univ ≠ ⊤`:

  `HasSum (fun i => ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f)
      (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
    ∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (νC i)`.

- `hasSum_twistedGeometricMeasures_term`, for `θ : G →* G`,
  `d : ∀ i, TwistedGeometricMeasures Γ θ (r i : G) μG` and `hfin : ∀ i, (d i).rational Set.univ ≠ ⊤`:

  `HasSum (fun i => (d i).term f) (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
    ∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (d i).orbital`.

- `integral_twistedKernelDiagonal_eq_sum_term`, the same for `r : Fin m → Γ`:

  `∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν = ∑ j, (d j).term f`.

  This is the hypothesis `t = ∑ j, (d j).term f` of `SingleOrbitGeometricTraceStatement` for
  `t = ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν`.

- `integral_twistedKernelDiagonal_expansion`, for `r : Fin m → Γ` and
  `hfinite : ∀ d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG, ∀ j, (d j).rational Set.univ ≠ ⊤`:

  `∀ d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG,
    (∀ j, (d j).rational Set.univ ≠ ⊤) ∧ ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν = ∑ j, (d j).term f`,

  which is literally the last hypothesis of `SingleOrbitGeometricTraceStatement`.

- `abstractSimpleTwistedTraceFormula_of_trace_eq_integral`: all the hypotheses of
  `AbstractSimpleTwistedTraceFormulaStatement` (for `G : Type u`, `θ : G ≃ₜ* G`,
  `hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ`, `r : Fin n → Γ`, the representation `π`, the trace-class
  hypothesis, the measures `μC`, `νC`, `νΓC`, …), in the order of the statement except that its
  support condition `hsupp` comes after the others, followed by

  `htrace : operatorTrace (R(f) ∘ I_θ) = ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν`,

  where `R(f) ∘ I_θ` is written as in the statement
  (`(integratedIsometricAction μG π hπnorm hπmeas f _).comp (twistOperator Γ θ hθΓ ν hθν)`); the
  conclusion is that of the statement:

  `operatorTrace (R(f) ∘ I_θ) = ∑ i, ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f`.

  The proof does not use the hypotheses `MeasurePreserving θ μG μG`, the identification of `π` with
  right translation, the trace-class hypothesis, the integrability of the twisted orbit functions
  (it is proved) and `IsOpenPosMeasure (μC i)`; `hθν`, `π`, `hπnorm`, `hπmeas` enter only through
  the operator whose trace `htrace` speaks of.

- `abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace`:

  `AbstractTwistedKernelDiagonalTraceStatement.{u} → AbstractSimpleTwistedTraceFormulaStatement.{u}`.

  `AbstractTwistedKernelDiagonalTraceStatement` (module
  `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement`) says that, for the data of
  `AbstractSimpleTwistedTraceFormulaStatement` up to and including its trace-class hypothesis, the
  trace of `R(f) ∘ I_θ` is `∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν`; this
  is `htrace`, and the support condition is a hypothesis of the trace formula statement.

## Proofs

For each `i`, `Γ ⊓ C_{r i}` is a discrete, hence closed, subgroup, the counting measure on it is a
regular Haar measure, and `compatibleMeasureExists` gives a measure `νr i` on `(Γ ⊓ C_{r i}) \ G`
compatible with `(μG, count)`; this is where right invariance of `μG` is used. The unfolding gives
`HasSum (i ↦ ∫_{(Γ ⊓ C_{r i}) \ G} f (x⁻¹ r i θ x) dνr i) (∫_{Γ \ G} K(x, x) dν)` and integrability.
Quotients in stages, for `Λ = Γ ⊓ C_{r i} ≤ H = C_{r i}` and `Λ' = Γ.subgroupOf C_{r i}` (whose elements
are those of `H` lying in `Λ`), turn each term into `(νΓC i univ).toReal · TO_{r i}(f)` and transfer
integrability. With `TwistedGeometricMeasures` the measures are the fields of `d i`. For finitely many
representatives, `HasSum` over `Fin m` is the finite sum (`hasSum_fintype`, `HasSum.unique`). The
abstract formula follows from `htrace` and the finite expansion for `θ : G ≃ₜ* G` (a
`MonoidHomClass`); with `htrace` supplied by `AbstractTwistedKernelDiagonalTraceStatement` it is
`AbstractSimpleTwistedTraceFormulaStatement`.

## What the abstract statement rests on

`AbstractSimpleTwistedTraceFormulaStatement` has the support condition among its hypotheses
(hypothesis 2 of its page); it holds for every `f` when `Γ \ G` is compact
(`exists_isCompact_twistedSupport_of_compactSpace`). By
`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace`, the statement follows from
`AbstractTwistedKernelDiagonalTraceStatement`: the trace of the trace-class operator `R(f) ∘ I_θ` is
the integral of the diagonal of its kernel `K(x, y) = Σ_γ f(x⁻¹ γ θ y)`. That statement is proved by
`abstractTwistedKernelDiagonalTrace` (module `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`),
from Brislawn's theorem in the Library's form (`traceClassContinuousKernelDiagonal`); Getz–Hahn,
§18.5, printed p. 488, cite [Bri91, Corollary 3.2] for it. So `AbstractSimpleTwistedTraceFormulaStatement`
is proved: `abstractSimpleTwistedTraceFormula` (module `Langlands.TraceFormula.AbstractSimpleTwistedProof`)
is `abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` applied to
`abstractTwistedKernelDiagonalTrace`. Neither half uses `MeasurePreserving θ μG μG`, and the analytic
half does not use the right invariance of `μG` either; it is used only here, for the compatible
measures on `(Γ ⊓ C_{r i}) \ G`.

## Declarations, in order

- `exists_isCompatible_count_inf` (private): a compatible measure on `(Γ ⊓ K) \ G`.
- `hasSum_twistedOrbitalIntegral_of_isCompatible`
- `hasSum_twistedGeometricMeasures_term`
- `integral_twistedKernelDiagonal_eq_sum_term`
- `integral_twistedKernelDiagonal_expansion`
- `abstractSimpleTwistedTraceFormula_of_trace_eq_integral`
- `abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace`

## Literature

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024): Theorem 18.2.5, printed p. 479,
  and its proof, printed pp. 481–482 (unfolding of `∫ K_f`, Lemma 17.8.5); §18.5, printed pp. 486–488,
  the twisted kernel `K_f(g, θ(h))` of `R(f) ∘ I_θ`, (18.32) the twisted orbital integral and
  `τ(C_γ^θ)`, the twisted trace (18.35) and Corollary 18.5.1, printed p. 488,
  `∑_π tr(π(f) ∘ I_θ) = ∑_{[γ]} τ(C_γ^θ) TO_γ(f)`. The book works with adelic groups, a finite-order
  `θ`, cuspidal image and central quotients `A_G`; here the group, the twist and the measures are
  general and the trace is related to the kernel only through `htrace`.
- Deligne–Kazhdan–Vignéras, in *Représentations des groupes réductifs sur un corps local* (1984),
  A.1.c, printed p. 44: the simple trace formula as the sum over conjugacy classes of
  `vol(Z_γ(F) Z(𝔸) \ Z_γ(𝔸)) · ∫_{Z_γ(𝔸) \ G(𝔸)} f(x⁻¹ γ x) dx`, for `θ = id`.

## Source and licence

This file contains no text of the repository `leanprover-community/riemann-hypothesis`; it combines
the Library's `twistedGeometricSide_unfolding` (whose page names the source) and
`IsCompatible.integral_descend_stages`.
