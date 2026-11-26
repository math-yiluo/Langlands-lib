# The simple trace formula for `GL_n` over a number field (proof)

Module `Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof`, namespace
`Langlands.TraceFormula`.

`generalLinearSimpleTraceFormula : GeneralLinearSimpleTraceFormulaStatement.{u}` proves the
published statement (module `Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement`,
whose page describes the data, the hypotheses and the conclusion) with its universe parameter
free and no added hypothesis. The module activates the statement module's two local instances
(`generalLinearSimpleTraceIsAffine`, `generalLinearSimpleTraceSmooth`) and repeats its local
notation `GLₙ`. Below, `G¹ = normOneSubgroup F GLₙ`, `Γ = rationalNormOneSubgroup F GLₙ`,
`ν = normOneRationalQuotientHaarMeasure F GLₙ`, and `L_v(g)` is the component
`FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g))`
of `g ∈ GL_n(𝔸_F)` at the finite place `v`.

## Auxiliary results of the module

- `isRegularElliptic_conj_iff x g`: `IsRegularElliptic (x⁻¹ * g * x) ↔ IsRegularElliptic g` in
  `GL_n(K)` for any field `K`, since conjugate matrices have the same characteristic polynomial
  (`Matrix.charpoly_units_conj'`).
- `localProjection_finite_adelicHomeomorph_congr F n v h`: if two points `y, z` of
  `AdelicGroupPoints F GLₙ` have the same group-scheme point at `v`
  (`atPlace F GLₙ (.inr v) y = atPlace F GLₙ (.inr v) z`), then `L_v(y) = L_v(z)`. Entrywise,
  both sides are the evaluation of the matrix-entry regular function `entrySection` at the
  point at `v` (`atPlace_evaluation` and `GroupScheme.GeneralLinear.affinePointsEquiv_entry_evaluation`).
- `isRegularElliptic_localProjection_normOne_conj_iff F n v x g`: for `x, g ∈ G¹`,
  `L_v(x⁻¹ g x)` is regular elliptic if and only if `L_v(g)` is, since `L_v` is multiplicative.
- `generalLinearNormOne_compact_closed F n v r hlocal`: for `r ∈ Γ` with `L_v(r)` regular
  elliptic, the quotient `(Γ ∩ C_r) \ C_r` of the centralizer `C_r` of `r` in `G¹` is compact
  (`IsCompactTwistedCentralizerQuotient` for the identity automorphism) and the conjugacy orbit
  of `r` in `G¹` is closed. The characteristic polynomial of the rational matrix of `r` is
  separable and irreducible over `F`, because its image over `F_v` is
  (`Polynomial.separable_map`, `Polynomial.Monic.irreducible_of_irreducible_map`); so `n ≠ 0`.
  Through the homeomorphism `GeneralLinearGroupPoints.normOneAdelicHomeomorph` with the
  determinant-norm-one matrices, compactness is `adelicRegularCentralizerCompactQuotient`
  (module `Langlands.TraceFormula.AdelicRegularCentralizerCompact`) and closedness is
  `isClosed_normOneRationalConjugacyOrbit` (module `Langlands.TraceFormula.AdelicRegularConjugacy`).
  This is the geometric half of the proof of `generalLinearEllipticCentralizer` (module
  `Langlands.TraceFormula.GeneralLinearEllipticCentralizerProof`); the two private transport
  lemmas of the module repeat the private lemmas used there.

## Proof of `generalLinearSimpleTraceFormula`

1. **The test function.** `f = f₁ * f₂` is continuous with compact support
   (`Langlands.Analysis.continuous_convolution_compactlySupported` and
   `Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`, module
   `Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction`) and is bundled as an
   element of `C_c(GL_n(𝔸_F), ℂ)`.
2. **Trace class.** `groupSchemeFullL2TraceClass` (module
   `Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof`), applied to `GLₙ` with the given
   `hPD, hG, T, i, hi, I, e, hc` and hypotheses 1 and 2, gives `h : Integrable f μG` with
   `R(f) = haarQuotientL2IntegratedAction … μG f h` trace class. This `h` is the integrability
   proof of the conclusion.
3. **The norm-one quotient.** `π = quotientRightRegular Γ ν _` (module
   `Langlands.TraceFormula.QuotientRightRegular`) is the right regular representation of `G¹` on
   `L²(Γ \ G¹, ν)`, built from the right invariance in
   `normOneRationalQuotientHaarMeasure_isCompatible`; it is isometric, has strongly measurable
   orbits and acts by right translation almost everywhere. `positiveQuotientTraceComparison`
   (module `Langlands.TraceFormula.PositiveQuotientTraceComparisonProof`) then shows that `fOne`
   is continuous with compact support (it is bundled as `fOneC ∈ C_c(G¹, ℂ)`), that `π(fOne)` is
   trace class, and that `tr R(f) = tr π(fOne)`.
4. **The trivial twist.** With `θ = ContinuousMulEquiv.refl G¹`, the induced map of `Γ \ G¹` is
   the identity, so it preserves `ν`, and `twistOperator Γ θ _ ν _` is the identity operator
   (`twistOperator_coeFn`). The twisted centralizers, orbit functions, conjugacy relation and
   orbital integrals for `θ` and for `MonoidHom.id G¹` agree definitionally, so the measures and
   measurable structures of the conclusion are passed to the abstract formula unchanged.
5. **A compact set of regular elliptic points.** `positiveAverageOrbitSupport` (module
   `Langlands.TraceFormula.PositiveAverageOrbitSupport`), applied to `Ω = tsupport f` and the
   measure `normalizedPositiveHaarMeasure`, gives a compact `Ω₁ ⊆ G¹` containing every `z` with
   `fOne z ≠ 0`, each point of which has the same group-scheme points at all finite places as
   some point of `tsupport f`. By hypothesis 3 and
   `localProjection_finite_adelicHomeomorph_congr`, `L_v(z)` is regular elliptic for every
   `z ∈ Ω₁`.
6. **Finitely many classes.** `generalLinearEllipticClassFiniteness` (module
   `Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessProof`), applied to the compact
   image of `Ω₁` in `AdelicGL F n`, gives a finite set `R` of rational matrices such that every
   rational matrix with an adelic conjugate in that image is `GL_n(F)`-conjugate to a member of
   `R`. The surjective homomorphism `ψ : GL_n(F) → Γ`, the inverse of
   `GeneralLinearGroupPoints.rationalEquiv` followed by `rationalNormOne`, is compatible with
   `adelicHomeomorph` (`GeneralLinearGroupPoints.adelicHomeomorph_rational`). Let `S ⊆ Γ` be the
   set of `q` with `fOne(x⁻¹ q x) ≠ 0` for some `x ∈ G¹`. If `q = ψ(γ) ∈ S`, then
   `x⁻¹ q x ∈ Ω₁`, so `γ` is conjugate to some `r ∈ R` and `q` is conjugate in `Γ` to `ψ(r)`.
   Hence the set of conjugacy classes of `Γ` (Mathlib's `ConjClasses Γ`) meeting `S` is finite.
7. **Representatives.** The finitely many classes are enumerated by `Fin m`, and `r j ∈ S` is a
   chosen element of the `j`-th class. Distinct indices give non-conjugate elements, and every
   `q ∈ S` is conjugate in `Γ` to some `r j`; these are the first and third clauses of the
   conclusion, since `IsTwistedConjugate Γ (MonoidHom.id G¹) δ δ'` says `δ' = h⁻¹ δ h` for some
   `h ∈ Γ`. As `r j ∈ S`, some conjugate `x⁻¹ (r j) x` lies in `Ω₁`, so `L_v(r j)` is regular
   elliptic by step 5 and `isRegularElliptic_localProjection_normOne_conj_iff` (second clause).
8. **The support condition.** By `generalLinearNormOne_compact_closed`, each `r j` has a closed
   orbit and a compact rational centralizer quotient. `exists_isCompact_twistedSupport` (module
   `Langlands.TraceFormula.TwistedSupportCompact`), applied to `fOne` (whose closed support is
   compact) and the covering property of step 7, gives the support hypothesis of the abstract
   formula: a compact `C ⊆ G¹` with `x ∈ Γ · C` whenever `fOne(x⁻¹ γ x) ≠ 0` for some `γ ∈ Γ`.
9. **Volumes and integrability.** For the measures of the conclusion,
   `generalLinearEllipticCentralizer` (module
   `Langlands.TraceFormula.GeneralLinearEllipticCentralizerProof`), applied to each `r j`, gives
   `νΓC j univ ≠ ⊤` and the `νC j`-integrability of the orbit function of the compactly supported
   continuous `fOne`. These are the first two parts of the final clause.
10. **The trace identity.** `abstractSimpleTwistedTraceFormula` (module
   `Langlands.TraceFormula.AbstractSimpleTwistedProof`), applied to `G¹` with `Measure.haar`
   (right invariant by the statement's instance hypothesis), `Γ` (discrete,
   `rationalNormOneSubgroup_discreteTopology`), `ν`, `θ`, `π`, `fOneC` and the data of steps
   3–9, gives `tr(π(fOne) ∘ I_θ) = ∑ j, vol((Γ ∩ C_j) \ C_j) · O_{r j}(fOne)`. With `I_θ = 1`
   (step 4) and `tr R(f) = tr π(fOne)` (step 3) this is the identity of the conclusion.
   `G¹` is Hausdorff, locally compact (`normOneLocallyCompactSpace`) and second countable
   (`normOneSecondCountableTopology`), hence σ-compact.

The argument needs no case distinction on `n`. The proof uses `set_option maxHeartbeats 1000000`
for the main theorem.

## Correspondence with the sources

The statement is the Library's form of the simple trace formula of Deligne and Kazhdan,
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered
`getz-hahn-2024-automorphic-representations`, Corollary 18.4.1 (printed p. 485, PDF p. 492); its
page gives the correspondence of the data and measures. The implemented route follows the
structure of the source's derivation: Corollary 18.4.1 is the case `H = ΔG` of the general simple
relative trace formula, Theorem 18.2.5 (printed p. 479, PDF p. 486), whose hypotheses on closed
orbits and finite centralizer volumes (18.14) are steps 8 and 9 here, and the finiteness of the
classes meeting a compact set is the analogue of Lemma 18.2.6 (printed p. 479) in step 6. The
passage between functions on `G(𝔸_F)` and on `A_G \ G(𝔸_F) ≅ G(𝔸_F)¹`, (2.19)–(2.22) (printed
pp. 68–69), is step 3. The analytic identity itself (the trace as the integral of the kernel on
the diagonal and its unfolding over classes) is not reproved here: it is the Library's abstract
simple twisted trace formula, used with the trivial twist.
