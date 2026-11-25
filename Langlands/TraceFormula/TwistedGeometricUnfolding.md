# Unfolding the integral of the diagonal of the twisted kernel

Module `Langlands.TraceFormula.TwistedGeometricUnfolding`, namespace `Langlands.TraceFormula`.

The twisted kernel of `TwistedOrbital` is `K(x, y) = ∑' γ : Γ, f (x⁻¹ γ θ y)` and its diagonal,
descended to `Γ \ G`, is `twistedKernelDiagonal Γ θ hθΓ f`. This module proves the first half of the
geometric side of the simple twisted trace formula: the integral of the diagonal over `Γ \ G` is the
sum, over representatives `r i` of the `Γ`-`θ`-conjugacy classes, of the integrals of
`x ↦ f (x⁻¹ r i θ x)` over `(Γ ∩ C_{r i}) \ G`, where `C_δ = twistedCentralizer θ δ`. The passage from
`(Γ ∩ C_{r i}) \ G` to `C_{r i} \ G` (quotients in stages) is `QuotientInStages`; the two together
are assembled in `TwistedGeometricSide`.

## Statements

`G` is a group, `Θ` a type with `[FunLike Θ G G] [MonoidHomClass Θ G G]` and `θ : Θ`; so `θ` may be
a monoid endomorphism, an automorphism or a continuous automorphism, as in `TwistedOrbital`.

- `apply_twistedConj_left_mul_of_le hH f c x`, for `hH : H ≤ twistedCentralizer θ δ`, `f : G → A`,
  `c : H`, `x : G`:

  `f ((c.val * x)⁻¹ * δ * θ (c.val * x)) = f (x⁻¹ * δ * θ x)`.

  It is the invariance proof by which `x ↦ f (x⁻¹ * δ * θ x)` descends to `LeftQuotient H`; below it
  is used with `H = Γ ⊓ twistedCentralizer θ δ` and `hH = inf_le_right`.

- `exists_isCompact_twistedSupport_of_compactSpace Γ hΓ θ f`, for `G` a locally compact topological
  group, `hΓ : IsClosed (Γ : Set G)`, `[CompactSpace (LeftQuotient Γ)]`, `f : G → ℂ`:

  `∃ C : Set G, IsCompact C ∧ ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y`.

- `twistedGeometricSide_unfolding μG Γ ν hν θ hθ hθΓ f hsupp r hr hcover νr hνr`. Hypotheses: `G` a
  topological group, Hausdorff, locally compact, second countable, with its Borel σ-algebra;
  `μG : Measure G` with `[μG.IsHaarMeasure]`; `Γ : Subgroup G` with `[DiscreteTopology Γ]`;
  `[MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]`;
  `hν : IsCompatible Γ μG Measure.count ν`; `hθ : Continuous θ`; `hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ`;
  `f : C_c(G, ℂ)`;

  `hsupp : ∃ C : Set G, IsCompact C ∧ ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y`;

  `r : ι → Γ` (any type `ι`) with
  `hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j` and
  `hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) → ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G)`;
  measurable Borel structures on each `LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G))`, and
  `hνr : ∀ i, IsCompatible (Γ ⊓ twistedCentralizer θ (r i : G)) μG Measure.count (νr i)`. Conclusion:

  `HasSum (fun i => ∫ q, descend (Γ ⊓ twistedCentralizer θ (r i : G)) (fun x => f (x⁻¹ * (r i : G) * θ x))
      (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νr i)
    (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
  ∀ i, Integrable (descend (Γ ⊓ twistedCentralizer θ (r i : G)) (fun x => f (x⁻¹ * (r i : G) * θ x))
      (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) (νr i)`.

- `twistedGeometricSide_unfolding_of_compactSpace`: the same conclusion with
  `[CompactSpace (LeftQuotient Γ)]` and without `hsupp`.

No right invariance of `μG` is assumed. `IsTwistedConjugate Γ θ δ δ'` is the Library's
`∃ h ∈ Γ, h⁻¹ * δ * θ h = δ'`.

## Proofs

**Normalizing function.** `Γ` is closed and countable, and the counting measure on `Γ` is finite on
compacts and positive on open sets, so `exists_continuous_isNormalizingFunction`
(`QuotientNormalizingFunction`) gives a continuous `ρ₀ : G → ℝ≥0` with `∑' γ : Γ, ρ₀ (γ x) = 1` for
all `x`. It plays the part of the indicator of a fundamental domain.

**Finiteness.** `Φ x = ∑' γ : Γ, ‖f (x⁻¹ γ θ x)‖` is left `Γ`-invariant (reindexing by
`γ ↦ g⁻¹ γ θ g`), vanishes outside `Γ · C` by `hsupp`, and is bounded on `C` by `M = N · sup ‖f‖`,
where only the `N` elements of the finite set `{γ | ∃ y ∈ C, f (y⁻¹ γ θ y) ≠ 0}` contribute (it is
finite because the compact set `{y z θ(y)⁻¹ | y ∈ C, z ∈ supp f}` meets the discrete closed `Γ` in a
finite set). By the rule of `QuotientNormalizingFunction`,
`∑' γ, ∫ ‖f (x⁻¹ γ θ x)‖ ρ₀ x dμG = ∫ Φ ρ₀ dμG = ∫_{Γ \ G} Φ dν ≤ M ν(image of C) < ∞`.

**The diagonal.** Hence each `F γ x = ρ₀ x • f (x⁻¹ γ θ x)` is integrable with summable norms, and
`HasSum (γ ↦ ∫ F γ) (∫ ∑' γ, F γ)` (`hasSum_integral_of_summable_integral_norm`). The rule again gives
`∫ ∑' γ, F γ dμG = ∫ ρ₀ x K(x, x) dμG = ∫_{Γ \ G} K(x, x) dν`; `K(x, x)` is measurable as a countable sum
of continuous functions.

**One class.** For `δ ∈ Γ` choose `d c ∈ Γ` with `(d c)⁻¹ δ θ (d c) = c` for each `c` in the class of
`δ`. The map `(η, c) ↦ (d c)⁻¹ η` from `(Γ ⊓ C_δ) × class(δ)` to `Γ` is bijective (inverse
`γ ↦ (d c' γ, c')` with `c' = γ δ θ(γ)⁻¹`). So `ρ_δ x = ∑' c, ρ₀ ((d c)⁻¹ x)` satisfies
`∑' η ∈ Γ ⊓ C_δ, ρ_δ (η x) = ∑' γ ∈ Γ, ρ₀ (γ x) = 1`: it is a normalizing function for `Γ ⊓ C_δ`. By
the rule, `∫_{(Γ ⊓ C_δ) \ G} f (x⁻¹ δ θ x) = ∫ ρ_δ x f (x⁻¹ δ θ x) dμG = ∑ c, ∫ ρ₀ ((d c)⁻¹ x) f (x⁻¹ δ θ x) dμG`,
and the substitution `x = d c · y` (left invariance of `μG`) turns the term of `c` into
`∫ ρ₀ y f (y⁻¹ c θ y) dμG`, the term of `c` in the diagonal. Integrability on `(Γ ⊓ C_δ) \ G` follows from
the same computation with absolute values, bounded by the finiteness above.

**Regrouping.** The map `Σ i, class(r i) → Γ` is injective by `hr`, and the terms of `Γ` outside its
image vanish by `hcover`; `HasSum.sigma` gives the conclusion.

**Cocompact case.** If `Γ \ G` is compact it is the image of a compact `C ⊆ G`
(`leftQuotient_exists_isCompact_image`), and every `x` is `g y` with `g ∈ Γ`, `y ∈ C`.

## Declarations, in order

- `apply_twistedConj_left_mul_of_le`
- `twistedConjEquiv`, `twistedConjEquiv_apply`, `tsum_twistedConj_left_mul` (private): reindexing
  of `Γ` by `γ ↦ g⁻¹ γ θ g`.
- `bijective_classMap` (private): the bijection `(Γ ⊓ C_δ) × class(δ) → Γ`.
- `exists_isCompact_twistedSupport_of_compactSpace`
- `finite_twistedSupport` (private)
- `leftQuotientMap_mul_of_mem`, `isTwistedConjugate_symm`, `isTwistedConjugate_trans`,
  `isClosed_twistedCentralizer'`, `enorm_nnreal_smul`, `countable_of_discreteTopology`,
  `count_isFiniteMeasureOnCompacts`, `count_isOpenPosMeasure` (private helpers).
- `tsum_lintegral_twisted_ne_top` (private): the finiteness.
- `hasSum_twistedClass` (private): one class.
- `twistedGeometricSide_unfolding`
- `twistedGeometricSide_unfolding_of_compactSpace`

## Literature

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §17.8, proof of Theorem 17.8.7,
  printed pp. 468–469: the integral over `AH(F) \ H(𝔸_F)` of the sum over `γ` is unfolded into a sum
  over classes `[γ]` of integrals over `AH_γ(F) \ H(𝔸_F)`, then split into
  `τ(H_γ) · RO_γ(f)`. §18.2, proof of Theorem 18.2.5, printed pp. 481–482, applies it to the kernel
  `K_f(g, h) = ∑ f(g⁻¹ γ h)`, and §18.5, printed pp. 486–488, (18.30)–(18.33) and Corollary 18.5.1,
  specializes it to `θ`-conjugation, the kernel of `R(f) ∘ I_θ` being `K_f(g, θ(h))`. The book's groups
  are adelic and its quotients are by central split tori; here `G`, `Γ`, `θ` are general and the
  quotient measures are explicit.
- Deligne–Kazhdan–Vignéras, in *Représentations des groupes réductifs sur un corps local* (1984),
  A.1.b–c, printed pp. 42–44: the kernel `∑_γ f(x⁻¹ γ y)` (p. 42), the trace as the integral of the
  diagonal (p. 43), and on p. 44 the remark that `x ↦ ∑_γ |f(x⁻¹ γ x)|` has compact support modulo
  `Z(𝔸) G(F)`, so that sum and integral may be exchanged and the `γ` grouped by conjugacy class
  (A.1.c). The hypothesis `hsupp` is this compactness of support.

## Source and licence

Port, in part, of
`src/Development/AutomorphicArithmetic/Foundations/Convolution/LocalGroupAnalysis/TwistedGeometricSideUnfolding.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b` (the proof of the source's statement
`PositivityTheory.Rg.Tf.Geo.U1`). The repository has no licence file; its text is used with
attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

- Lines 12–17 (`twEquiv`, `twEquiv_apply`) become `twistedConjEquiv`, `twistedConjEquiv_apply`;
  lines 28–39 (`finite_meet`) become `finite_twistedSupport`; the bound of lines 41–77
  (`tsum_lintegral_ne_top`) becomes `tsum_lintegral_twisted_ne_top`; the regrouping at the end of the
  main proof (lines 227–268: the injective map from the sigma type of classes, the vanishing terms,
  `HasSum.sigma`) is kept.
- The source integrates over a measurable fundamental domain of `Γ` (`fundamentalDomain`,
  `quotientMeasure` of `GroundTheory/AutomorphicForms/QuotientMeasure.lean`) and writes integrands with
  `Quotient.out`. Here the indicator of the fundamental domain is replaced by a continuous normalizing
  function `ρ₀` of `Γ`, the quotient measures are any measures compatible in the Library's sense, and
  integrals over quotients are turned into integrals over `G` by the rule of
  `QuotientNormalizingFunction`. Accordingly the source's lines 79–133 (`isFund`, the fundamental
  domain `⋃ d • D` of `Γ ∩ C_γ`, and `integrable_quot_iff`) are replaced by `bijective_classMap` and the
  normalizing function `ρ_δ = ∑' c, ρ₀ ((d c)⁻¹ ·)`, and `one_class` (lines 135–222) by
  `hasSum_twistedClass`, whose computation is new.
- The twist `θ : X →* X` becomes any `θ : Θ` with `[MonoidHomClass Θ G G]`; `Type` becomes a universe
  variable; the right invariance of `μG` and the instance `DiscreteTopology (Γ ⊓ C)` are not assumed;
  the measurable structures on the quotients are instance arguments; names and docstrings are the
  Library's; the cocompact lemma and corollary are new.
