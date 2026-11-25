# `R(f) ∘ I_θ` as an integral operator on `Γ \ G`

Module `Langlands.TraceFormula.TwistedKernelOperator`, namespace `Langlands.TraceFormula`.

The module descends the twisted kernel `K(x, y) = Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y))` (`twistedKernel`,
module `Langlands.TraceFormula.TwistedOrbital`) to `Γ \ G × Γ \ G` and proves three facts about it:
it is continuous, `R(f) ∘ I_θ` is the integral operator with this kernel, and the kernel is in
`L²(ν × ν)` when the operator is Hilbert–Schmidt, in particular when it is trace class. These are
the hypotheses of Brislawn's theorem (`TraceClassContinuousKernelDiagonalStatement`). It is applied in
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`.

Notation: `π̄ : G → Γ \ G` is the projection (`Quotient.mk _`, `leftQuotientMap Γ`), and
`θ̄ = quotientAutomorphism Γ θ hθΓ` is the homeomorphism `Γ x ↦ Γ θ(x)`. `R(f)` is
`Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f hf` with
`hf = f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport`, and
`I_θ = twistOperator Γ θ hθΓ ν hθν` (`I_θ φ = φ ∘ θ̄⁻¹`).

## Statements

### The kernel on the quotient

For `G : Type u` a group, `F` with `[FunLike F G G] [MonoidHomClass F G G]`, `Γ : Subgroup G`,
`θ : F`, `hθ : ∀ γ ∈ Γ, θ γ ∈ Γ` and `f : G → ℂ`:

- `twistedQuotientKernel Γ θ hθ f : LeftQuotient Γ → LeftQuotient Γ → ℂ` is the descent of
  `twistedKernel Γ θ f` in both variables (`Quotient.lift₂`). It is well defined because
  `twistedKernel` is left `Γ`-invariant in each variable (`twistedKernel_left_mul_left`,
  `twistedKernel_left_mul_right`).
- `twistedQuotientKernel_mk` (simp):
  `twistedQuotientKernel Γ θ hθ f (Quotient.mk _ x) (Quotient.mk _ y) = twistedKernel Γ θ f x y`.
- `twistedQuotientKernel_self`, for `q : LeftQuotient Γ`:
  `twistedQuotientKernel Γ θ hθ f q q = twistedKernelDiagonal Γ θ hθ f q`.

### Local finiteness and continuity

`G` is a topological group, `[T2Space G]`, `Γ` has `[DiscreteTopology Γ]`, and `f : C_c(G, ℂ)`.

- `finite_twistedKernel_support` (for `θ : F` with only `[FunLike F G G]`,
  `hθ : Continuous θ`, `hA : IsCompact A`, `hB : IsCompact B`):
  `{γ : Γ | ∃ x ∈ A, ∃ y ∈ B, f (x⁻¹ * γ * θ y) ≠ 0}.Finite`.
- `hasFiniteSupport_twistedKernel_terms` (same `θ`, `hθ`; `x y : G`):
  `Function.HasFiniteSupport (fun γ : Γ => f (x⁻¹ * γ * θ y))`.
- `continuous_uncurry_twistedKernel` (`[LocallyCompactSpace G]`, same `θ`, `hθ`):
  `Continuous (Function.uncurry (twistedKernel Γ θ (f : G → ℂ)))`.
- `continuous_uncurry_twistedQuotientKernel` (`[LocallyCompactSpace G]`,
  `[MonoidHomClass F G G]`, `hθ : Continuous θ`, `hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ`):
  `Continuous (Function.uncurry (twistedQuotientKernel Γ θ hθΓ (f : G → ℂ)))`.
- `twistedQuotientKernel_mk_eq_zero`, for a topological space `G`, `θ : G ≃ₜ* G`,
  `hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ`, `f : G → ℂ`, `x : G`, `q : LeftQuotient Γ` and
  `hq : q ∉ leftQuotientMap Γ '' (θ.symm '' ((fun c => x * c) '' tsupport f))`:
  `twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f (Quotient.mk _ x) q = 0`.

### The operator

Common data from here on: `G : Type u` a topological group, Hausdorff, locally compact, second
countable, with `[MeasurableSpace G] [BorelSpace G]`; `μG : Measure G` with `[μG.IsHaarMeasure]`;
`Γ : Subgroup G` with `[DiscreteTopology Γ]`; `[MeasurableSpace (LeftQuotient Γ)]
[BorelSpace (LeftQuotient Γ)]`; `ν : Measure (LeftQuotient Γ)` with
`hν : IsCompatible Γ μG Measure.count ν`; `θ : G ≃ₜ* G` with `hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ` and
`hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν`; `f : C_c(G, ℂ)`. The
representation is `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` with
`hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖`,
`hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG` and
`hπ : ∀ (g : G) (φ : Lp ℂ 2 ν), (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q)`.
These are the data of `AbstractTwistedKernelDiagonalTraceStatement` without
`[μG.IsMulRightInvariant]` and without `MeasurePreserving θ μG μG`.

- `quotientAverage_count_star_eq` (`θ : F` with `[FunLike F G G]`, `hθ : Continuous θ`,
  `x y : G`):

  `quotientAverage Γ Measure.count (fun b => star (f (x⁻¹ * b))) (Quotient.mk _ (θ y)) =
    star (twistedKernel Γ θ (f : G → ℂ) x y)`.

- `integral_mul_twistOperator_eq` (`μG`, `Γ`, `ν`, `hν`, `θ`, `hθΓ`, `hθν`, `f`, `x : G`,
  `φ : Lp ℂ 2 ν`):

  `∫ a, f a * (twistOperator Γ θ hθΓ ν hθν φ : LeftQuotient Γ → ℂ) (Quotient.mk _ (x * a)) ∂μG =
    ∫ q, twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) (Quotient.mk _ x) q * φ q ∂ν`.

- `twistedKernelOperator_ae_eq` (all the common data, `φ : Lp ℂ 2 ν`): the kernel representation,

  `(((integratedIsometricAction μG π hπnorm hπmeas f hf).comp (twistOperator Γ θ hθΓ ν hθν)) φ :
      LeftQuotient Γ → ℂ) =ᵐ[ν]
    fun q => ∫ q', twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q q' * φ q' ∂ν`.

  In words: `(R(f) I_θ φ)(q) = ∫ K(q, q') φ(q') dν(q')` for `ν`-almost every `q`.

### Square integrability

- `memLp_twistedQuotientKernel_row` (for `G` a Hausdorff locally compact group,
  `[MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]`,
  `ν` with `[IsFiniteMeasureOnCompacts ν]`, `θ : G ≃ₜ* G`, `hθΓ`, `f : C_c(G, ℂ)`,
  `q : LeftQuotient Γ`, `p : ℝ≥0∞`):
  `MemLp (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q) p ν`.
- `memLp_uncurry_twistedQuotientKernel_of_isHilbertSchmidt` (all the common data, and
  `hhs : IsHilbertSchmidt ((integratedIsometricAction μG π hπnorm hπmeas f hf).comp
  (twistOperator Γ θ hθΓ ν hθν))`):
  `MemLp (Function.uncurry (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ))) 2 (ν.prod ν)`.
- `memLp_uncurry_twistedQuotientKernel` (all the common data, and
  `htc : IsTraceClass ((integratedIsometricAction μG π hπnorm hπmeas f hf).comp
  (twistOperator Γ θ hθΓ ν hθν))`): the same conclusion,
  `MemLp (Function.uncurry (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ))) 2 (ν.prod ν)`.

No compactness of `Γ \ G` is assumed anywhere.

## Proofs

- **Finiteness.** If `f(x⁻¹ γ θ(y)) ≠ 0` with `x ∈ A`, `y ∈ B`, then
  `γ = x · (x⁻¹ γ θ(y)) · θ(y)⁻¹` lies in the image of the compact set `A × supp f × B` under the
  continuous map `(x, c, y) ↦ x c θ(y)⁻¹`. A discrete subgroup meets a compact set in finitely
  many points (`Subgroup.tendsto_coe_cofinite_of_isDiscrete`).
- **Continuity.** Each point `(x₀, y₀)` has a neighbourhood `A × B` with `A`, `B` compact, and on
  it only finitely many terms are nonzero. So the family of supports is locally finite, the sum is
  the `finsum` (`tsum_eq_finsum`), and `continuous_finsum` applies. On the quotient,
  `π̄ × π̄` is an open quotient map (`IsOpenQuotientMap.prodMap`), and the composite of the
  descended kernel with it is `twistedKernel`.
- **Rows.** If `K(Γ x, Γ y) ≠ 0`, some term `f(x⁻¹ γ θ(y))` is nonzero. Put
  `c = x⁻¹ γ θ(y) ∈ supp f`. Then `y = θ⁻¹(γ⁻¹) θ⁻¹(x c)` with `θ⁻¹(γ⁻¹) ∈ Γ`, so
  `Γ y ∈ π̄(θ⁻¹(x · supp f))`, a compact set. The coset space is Hausdorff (`leftQuotient_t2Space`).
  A continuous function vanishing off a compact set is in every `Lᵖ` for a measure finite on
  compact sets (`Continuous.memLp_of_hasCompactSupport`). `ν` is finite on compact sets because it
  is regular (`IsCompatible.regular`).
- **The orbit average.** For the counting measure the orbit integral of a function with finitely
  many nonzero values is the sum (`integral_countable`, `integrable_count_iff`). Its value at
  `Γ θ(y)` is `Σ_γ conj f(x⁻¹ γ θ(y)) = conj K(x, y)`.
- **The pairing (`integral_mul_twistOperator_eq`).** Apply `quotientL2Unfolding` (module
  `Langlands.Analysis.Local.QuotientL2UnfoldingProof`) to `k = conj f(x⁻¹ ·) ∈ C_c(G)`. It gives
  `v ∈ L²(ν)` with `v =ᵐ quotientAverage Γ count k` and `⟪v, ψ⟫ = ∫ conj k(g) ψ(Γ g) dμG(g)` for
  every `ψ ∈ L²(ν)`. With `ψ = I_θ φ` and left invariance of `μG`,
  `∫ f(a) ψ(Γ x a) da = ⟪v, ψ⟫`. Since `ψ =ᵐ φ ∘ θ̄⁻¹` (`twistOperator_coeFn`) and `θ̄⁻¹` preserves
  `ν` (`MeasurePreserving.integral_comp'`), `⟪v, ψ⟫ = ∫ φ(p) conj v(θ̄ p) dν(p)`. Also `θ̄` preserves
  `ν` (`MeasurePreserving.symm`), so `v ∘ θ̄ =ᵐ quotientAverage Γ count k ∘ θ̄`. By the previous step
  that function is `conj K(Γ x, ·)`. Working with pairings in `L²(ν)` avoids transporting
  almost-everywhere equalities along the maps `g ↦ Γ x g`.
- **The kernel representation.** `Langlands.Analysis.integratedTranslationPointwise` (module
  `Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof`) applies to the action
  `(q, g) ↦ rightTranslate Γ g q`. That action is continuous through the open quotient map
  `G × G → Γ \ G × G`, hence measurable since `Γ \ G` is second countable, and it preserves `ν`
  (`IsCompatible.right_invariant`). The theorem gives
  `R(f) ψ =ᵐ (q ↦ ∫ f(g) ψ(q g) dμG(g))`. At `q = Γ x` this integral is the pairing above, by
  `Quotient.inductionOn`.
- **Square integrability.** Apply `memLp_uncurry_of_isHilbertSchmidt` (module
  `Langlands.Analysis.HilbertSchmidtIntegralKernel`). Joint measurability comes from continuity
  (product Borel structure on the second-countable `Γ \ G × Γ \ G`). The rows are in `L²` by the
  row lemma, and the integral formula is the kernel representation. The Borel σ-algebra of the
  second-countable `Γ \ G` is countably generated, and `ν` is σ-finite, being finite on compact sets
  of the σ-compact `Γ \ G`. In the trace-class form, trace class implies Hilbert–Schmidt
  (`traceClassHilbertSchmidt`).

## Declarations, in order

- `twistedQuotientKernel`
- `twistedQuotientKernel_mk`
- `twistedQuotientKernel_self`
- `finite_twistedKernel_support`
- `hasFiniteSupport_twistedKernel_terms`
- `continuous_uncurry_twistedKernel`
- `continuous_uncurry_twistedQuotientKernel`
- `twistedQuotientKernel_mk_eq_zero`
- `countable_of_discreteTopology` (private): a discrete subgroup of a second-countable group is
  countable.
- `integral_count_eq_tsum` (private): the integral of a finitely supported function for the
  counting measure on a countable type is its sum.
- `quotientAverage_count_star_eq`
- `integral_mul_twistOperator_eq`
- `twistedKernelOperator_ae_eq`
- `memLp_twistedQuotientKernel_row`
- `memLp_uncurry_twistedQuotientKernel_of_isHilbertSchmidt`
- `memLp_uncurry_twistedQuotientKernel`

## Literature

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), §18.5, printed
  p. 487: (18.33), `I_θ φ = (g ↦ φ(θ⁻¹(g)))`, and "the composite `R(f) ∘ I_θ` … has kernel function
  `K_f(g, θ(h))`". The book works on `L²([G])` for a reductive group over a number field. Here the
  group, the discrete subgroup and the measures are general, and `K(x, y) = Σ_γ f(x⁻¹ γ θ(y))` is
  `K_f(x, θ(y))`.
- N. Bourbaki, *Intégration*, Chapitres 7 et 8 (1963), Chap. VII, §2, no. 2, formula (3) (printed
  p. 42), Proposition 4 (printed pp. 43–44), Définition 1 and formula (7) (printed p. 44): the quotient
  `μ/β` of a measure on `X` by a measure `β` on a group `H` acting properly on the right,
  characterized by `∫_X f dμ = ∫_{X/H} (∫_H f(xξ) dβ(ξ)) d(μ/β)(ẋ)`. `IsCompatible Γ μG count ν` is
  this relation for `H = Γ` acting on the left of `G` and `β` the counting measure.
- C. Brislawn, *Traceable integral kernels on countably generated measure spaces*, Pacific J. Math.
  150 (1991), printed p. 230, (1.3), for the `L²` kernel of a Hilbert–Schmidt operator. Corollary 3.2
  (printed p. 237) asks for this kernel to be continuous at almost every diagonal point.
