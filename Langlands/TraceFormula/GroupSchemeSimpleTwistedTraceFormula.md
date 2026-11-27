# The simple twisted trace formula on `L²([G])` from closed twisted orbits

Module `Langlands.TraceFormula.GroupSchemeSimpleTwistedTraceFormula`, namespace
`Langlands.TraceFormula`.

## Statement

`groupSchemeSimpleTwistedTraceFormula F G T i hi I e hc τ hτ hfix` works with the following
data.

- `G` is a group scheme over a number field `F` with `[IsAffine G.X.left]` and
  `[LocallyOfFiniteType G.X.hom]`.
- `T, i, hi, I, e, hc` are the Library's data for `L²([G])`: a split torus `T` with a central
  homomorphism `i : T.toGrp ⟶ G` whose character restriction is injective with finite-index
  range. Haar measure on `G¹ = normOneSubgroup F G` is assumed right-invariant.
- `τ : Aut G` has finite order (`hτ : IsOfFinOrder τ`) and fixes the image of the torus
  (`hfix : i ≫ τ.asIso.hom = i`). Write `Θ = adelicAut F τ` on `G(𝔸_F)`, `θ = normOneAut F τ`
  on `G¹` and `Γ = rationalNormOneSubgroup F G`.

The conclusion first gives `hΘ` and `hΘμ`. `hΘ` says that `Θ` preserves the subgroup generated
by `A⁺` and `G(F)`. `hΘμ` says that the inverse of the induced map of `[G]` preserves
`positiveRationalQuotientHaarMeasure`. These are the data of `I_Θ = twistOperator … hΘ … hΘμ`.
Then, for every continuous compactly supported `f : G(𝔸_F) → ℂ` with integrability proof `h`
and trace class `R(f) = haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h`,
let `fOne(x) = ∫_{A⁺} f(a x) da` be its average for `normalizedPositiveHaarMeasure`. Let
`m : ℕ` and `r : Fin m → Γ` satisfy four hypotheses:

1. every twisted orbit `TwistedOrbit θ (r j)` is closed in `G¹`;
2. every quotient `(Γ ∩ C_j) \ C_j` of the twisted centralizer `C_j = twistedCentralizer θ (r j)`
   is compact;
3. distinct `r j` are not `θ`-twisted-conjugate under `Γ`;
4. every `q ∈ Γ` with `fOne(x⁻¹ q θ(x)) ≠ 0` for some `x ∈ G¹` is twisted-conjugate under `Γ`
   to some `r j`.

Then for all Borel structures and measures `μC, νC, νΓC` as in
`GeneralLinearSimpleTwistedTraceFormulaStatement` (each `νC j` compatible with Haar measure on
`G¹` and `μC j`, each `νΓC j` compatible with `μC j` and counting measure), the volumes
`νΓC j univ` are finite, the twisted orbit functions of `fOne` are `νC j`-integrable, and

```text
operatorTrace (R(f) ∘ I_Θ) = ∑ j, (νΓC j univ).toReal · twistedOrbitalIntegral θ (r j) (νC j) fOne.
```

The conclusion has the shape of the conclusion of
`GeneralLinearSimpleTwistedTraceFormulaStatement` for an arbitrary `G` and `τ`. That statement
instead derives the trace class property, the representatives and hypotheses 1–4 from its own
hypotheses.

## Proof

1. **Quotient comparison.** `positiveQuotientTwistedTraceComparison` (module
   `Langlands.TraceFormula.PositiveQuotientTwistedTraceComparisonProof`, proving
   `PositiveQuotientTwistedTraceComparisonStatement`) gives `hΘ`, `hΘμ` and the comparison of
   `R(f) ∘ I_Θ` on `L²([G])` with `π(fOne) ∘ I_θ` on `L²(Γ \ G¹, ν)`, where
   `ν = normOneRationalQuotientHaarMeasure F G`. It applies to any isometric representation
   `π` of `G¹` acting by right translation.
2. **The averaged function.** `positiveQuotientTraceComparison` (module
   `Langlands.TraceFormula.PositiveQuotientTraceComparisonProof`), applied to `f` bundled in
   `C_c(G(𝔸_F), ℂ)`, shows that `fOne` is continuous with compact support. It is bundled as
   `fOneC ∈ C_c(G¹, ℂ)` and is Haar integrable.
3. **The right regular representation.** `ν` is compatible with Haar measure and counting
   measure (`normOneRationalQuotientHaarMeasure_isCompatible`), hence regular and
   right-invariant. `Γ` is discrete (`isDiscrete_rationalNormOneSubgroup`), hence closed, so
   `Γ \ G¹` is Hausdorff (`leftQuotient_t2Space`) and locally compact
   (`leftQuotient_locallyCompactSpace`). `G¹` is σ-compact as a locally compact second
   countable group. The representation `π = quotientRightRegular Γ ν _` (module
   `Langlands.TraceFormula.QuotientRightRegular`) acts on `L²(Γ \ G¹, ν)` and is isometric
   (`norm_quotientRightRegular_apply`). Its orbits are strongly measurable
   (`aestronglyMeasurable_quotientRightRegular_apply`), and it acts by right translation
   almost everywhere (`quotientRightRegular_coeFn`).
4. **Trace class.** `R(f) ∘ I_Θ` is trace class, as trace class operators form a right ideal
   (`isTraceClass_precomp`, module `Langlands.Analysis.TraceClassIdealProof`). By step 1,
   `π(fOne) ∘ I_θ` is trace class with the same trace.
5. **Volumes and integrability.** `twistedCentralizerAnalyticConditions_of_compact_closed`
   (module `Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction`), applied
   to each `r j` with hypotheses 1 and 2, gives finiteness of `νΓC j univ` for every
   compatible `νΓC j`. It also gives `νC j`-integrability of the twisted orbit function of
   every continuous compactly supported function, in particular `fOne`.
6. **Support.** `exists_isCompact_twistedSupport` (module
   `Langlands.TraceFormula.TwistedSupportCompact`), applied to `fOne`, hypotheses 1, 2 and 4,
   gives a compact `C ⊆ G¹` with `x ∈ Γ · C` whenever `fOne(x⁻¹ γ θ(x)) ≠ 0` for some `γ ∈ Γ`.
7. **The abstract formula.** `abstractSimpleTwistedTraceFormula` (module
   `Langlands.TraceFormula.AbstractSimpleTwistedProof`, proving
   `AbstractSimpleTwistedTraceFormulaStatement`) is applied to `G¹` with `Measure.haar`, `Γ`,
   `ν`, `θ` and `π`. Its remaining inputs are:
   - `normOneAut_mem_rationalNormOneSubgroup_iff`: `θ` preserves `Γ`;
   - `measurePreserving_normOneAut`: `θ` preserves Haar measure, as `τ` has finite order;
   - `measurePreserving_rationalQuotientAut_symm`: the inverse of the induced map preserves
     `ν`;
   - `fOneC`, the trace class of step 4, the support set of step 6, hypotheses 3 and 4, the
     measures, and the volumes and integrability of step 5.

   It gives `tr(π(fOne) ∘ I_θ) = ∑ j, vol((Γ ∩ C_j) \ C_j) · TO_{r j}(fOne)`, and step 4
   transfers this to `tr(R(f) ∘ I_Θ)`.

The theorem uses `set_option maxHeartbeats 1000000`.

## Sources

This is the Library's form of the passage from Theorem 18.2.5 to Corollary 18.5.1 in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), registered
`getz-hahn-2024-automorphic-representations`. Theorem 18.2.5 (printed p. 479) is taken there
with trivial character and `H = {(g, θ(g))}`. The source's `θ`-semisimplicity (closed
`θ`-conjugation orbit, after (18.32), printed p. 487) is hypothesis 1. Hypothesis 2 is a compact
form of `θ`-ellipticity (finiteness of `τ(C^θ_γ)`), giving the finite volumes and the compact
support set. The operator `I_θ` is (18.33) and the identity is (18.36) (printed p. 488) with
its spectral side written as the single operator trace. The passage between `A_G \ G(𝔸_F)`
and `G¹` follows §2.6, (2.19)–(2.22) (printed pp. 68–69), and is the content of
`PositiveQuotientTwistedTraceComparisonStatement`.
