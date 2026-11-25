# Normalizing functions for a closed subgroup

Module `Langlands.Analysis.Local.QuotientNormalizingFunction`, namespace
`Langlands.QuotientIntegration`.

A compatible quotient measure `ν` on `H \ G` (`IsCompatible H μG μH ν`, module `QuotientMeasure`)
is defined through Weil's formula for compactly supported continuous functions. This module gives
the tool by which integrals over `H \ G` are computed on `G` itself: a *normalizing function*, a
measurable `ρ : G → ℝ≥0∞` whose integral along every coset `H g` is one. Such a function exists, can
be taken continuous with a support condition, and for any compatible `ν` the measure `ν` is the
image in `H \ G` of `ρ · μG`. No integral over the quotient is defined by a choice of `ρ`.

## Statements

`LeftQuotient H` is the space of cosets `H g` (`Langlands/Group/LeftQuotient.lean`),
`leftQuotientMap H g` the coset of `g`, and `descend H F hF : LeftQuotient H → A` the function
induced by `F : G → A` with `hF : ∀ h : H, ∀ g, F (h.val * g) = F g`.

- `IsNormalizingFunction H μH ρ`, for `H : Subgroup G`, `[MeasurableSpace H]`, `μH : Measure H` and
  `ρ : G → ℝ≥0∞`, is the structure with fields

  `measurable : Measurable ρ` and `lintegral_eq_one : ∀ g : G, ∫⁻ h, ρ (h.val * g) ∂μH = 1`.

- `quotientAverageENNReal H μH f : LeftQuotient H → ℝ≥0∞` (for `[MeasurableMul H]`,
  `[IsMulRightInvariant μH]`) is the fiber integral, with
  `quotientAverageENNReal_mk : quotientAverageENNReal H μH f (Quotient.mk _ g) = ∫⁻ h : H, f (h.val * g) ∂μH`.

- `isNormalizingFunction_count_iff H ρ` (for `[MeasurableSingletonClass H]`):

  `IsNormalizingFunction H Measure.count ρ ↔ Measurable ρ ∧ ∀ g : G, ∑' h : H, ρ (h.val * g) = 1`.

The next statements share the hypotheses: `G` a topological group, Hausdorff, locally compact and
second countable, with its Borel σ-algebra; `H : Subgroup G` with `hH : IsClosed (H : Set G)`,
`[MeasurableSpace H] [BorelSpace H]`; `[MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]`;
`μG : Measure G` with `[IsFiniteMeasureOnCompacts μG]`; `μH : Measure H` with
`[μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]`; `hν : IsCompatible H μG μH ν`.

- `IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal hH hν f hf`, Weil's formula for
  `f : G → ℝ≥0∞` measurable:

  `∫⁻ g, f g ∂μG = ∫⁻ q, quotientAverageENNReal H μH f q ∂ν`.

- `IsNormalizingFunction.ae_lt_top hH hν hρ : ∀ᵐ g ∂μG, ρ g < ⊤`.

- `IsCompatible.lintegral_descend_eq hH hν hρ F hFm hF`, for `hρ : IsNormalizingFunction H μH ρ` and
  `F : G → ℝ≥0∞` measurable and left `H`-invariant:

  `∫⁻ q, descend H F hF q ∂ν = ∫⁻ g, F g * ρ g ∂μG`.

- `IsCompatible.eq_map_withDensity hH hν hρ : ν = (μG.withDensity ρ).map (leftQuotientMap H)`.

- `IsCompatible.lintegral_eq_lintegral_mul_comp hH hν hρ hφ`, for `φ : LeftQuotient H → ℝ≥0∞`
  measurable: `∫⁻ q, φ q ∂ν = ∫⁻ g, φ (leftQuotientMap H g) * ρ g ∂μG`.

- For `E` a real normed space and `φ : LeftQuotient H → E` with `hφ : AEStronglyMeasurable φ ν`:

  `IsCompatible.integrable_iff_integrable_smul_comp hH hν hρ hφ :
    Integrable φ ν ↔ Integrable (fun g => (ρ g).toReal • φ (leftQuotientMap H g)) μG`,

  `IsCompatible.integral_eq_integral_smul_comp hH hν hρ hφ :
    ∫ q, φ q ∂ν = ∫ g, (ρ g).toReal • φ (leftQuotientMap H g) ∂μG`.

- `measurable_descend hH F hFm hF : Measurable (descend H F hF)` for a measurable left
  `H`-invariant `F : G → Y`.

- For `E` a real normed space, second countable with its Borel σ-algebra (for instance `ℂ`), and
  `F : G → E` measurable and left `H`-invariant:

  `IsCompatible.integrable_descend_iff hH hν hρ F hFm hF :
    Integrable (descend H F hF) ν ↔ Integrable (fun g => (ρ g).toReal • F g) μG`,

  `IsCompatible.integral_descend_eq hH hν hρ F hFm hF :
    ∫ q, descend H F hF q ∂ν = ∫ g, (ρ g).toReal • F g ∂μG`.

- Independence of `ρ`: for two normalizing functions `ρ₁`, `ρ₂`,
  `IsCompatible.lintegral_mul_eq_of_isNormalizingFunction hH hν hρ₁ hρ₂ F hFm hF :
    ∫⁻ g, F g * ρ₁ g ∂μG = ∫⁻ g, F g * ρ₂ g ∂μG` and
  `IsCompatible.integral_smul_eq_of_isNormalizingFunction hH hν hρ₁ hρ₂ F hFm hF :
    ∫ g, (ρ₁ g).toReal • F g ∂μG = ∫ g, (ρ₂ g).toReal • F g ∂μG`.

- `exists_continuous_isNormalizingFunction H hH μH`, for `G` a Hausdorff, locally compact and
  σ-compact topological group with its Borel σ-algebra, `[MeasurableSpace H] [BorelSpace H]` and
  `[μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]`:

  `∃ ρ : G → ℝ≥0, Continuous ρ ∧ IsNormalizingFunction H μH (fun g => (ρ g : ℝ≥0∞)) ∧
    ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧
      ∀ h : H, ∀ x ∈ C, ρ (h.val * x) ≠ 0 → h.val * x ∈ C'`.

## Proofs

**Weil's formula.** `lintegral_orbitKernel` (module `QuotientWeilKernel`) states
`∫⁻ q, ∫⁻ g, f g ∂(orbitKernel H hH μH q) ∂ν = ∫⁻ g, f g ∂μG`, and the kernel at `H g` is the image of
`μH` under `h ↦ h g`, so the inner integral is `∫⁻ h, f (h g) ∂μH`. The measure `μH` is s-finite because
`H` is locally compact (closed in `G`) and second countable.

**Almost everywhere finite.** Apply Weil's formula to the indicator of `{ρ = ⊤}`: on each coset
`∫⁻ h, ρ (h g) ∂μH = 1 < ⊤`, so `ρ (h g) < ⊤` for `μH`-almost every `h`, the inner integral vanishes, and
`μG {ρ = ⊤} = 0`.

**The rule.** For `F` invariant, `∫⁻ h, F (h g) ρ (h g) ∂μH = F g · ∫⁻ h, ρ (h g) ∂μH = F g`; Weil's formula
for `F ρ` gives `∫⁻ descend F ∂ν = ∫⁻ F ρ ∂μG`. With `F = 1_A ∘ leftQuotientMap H` this is
`ν A = (ρ · μG)(π⁻¹ A)`, that is `ν = π_*(ρ · μG)`. The other forms follow from Mathlib's change of
variables (`lintegral_map`, `integrable_map_measure`, `integral_map`) and the density rules
(`lintegral_withDensity_eq_lintegral_mul`, `integrable_withDensity_iff_integrable_smul'`,
`integral_withDensity_eq_integral_toReal_smul`, which use `ρ < ⊤` almost everywhere). A descended
function is measurable by `measurable_quotient_iff`. Independence of `ρ` is the rule read twice.

**Existence.** Choose a compact exhaustion `K` of `G` with `K 0 = K 1 = ∅`. The sets `H · K m` are
closed and `H · interior (K m)` open; Urysohn's lemma gives `f m ∈ C_c(G)`, `0 ≤ f m ≤ 1`, equal to
`1` on the compact `K (m + 2) \ H · interior (K (m + 1))` and to `0` on `H · K m`. The family is locally
finite, `β = ∑ᶠ m, f m` is continuous, every coset meets `{β ≠ 0}` (take the least `n` with
`x ∈ H · interior (K n)`), and on `H · C`, `C ⊆ K N`, only `f 0, …, f (N - 1)` can be nonzero, so the
nonvanishing points lie in `⋃_{m < N} tsupport (f m)`. Then `h ↦ β (h x)` has compact support on `H`,
`D x = ∫ h, β (h x) ∂μH` is positive (positivity on open sets), left `H`-invariant (right invariance of
`μH`) and continuous (`continuousOn_integral_of_compact_support` on a compact neighbourhood), and
`ρ = β / D` is the normalizing function.

## Declarations, in order

- `quotient_mk_mul_of_mem` (private): `H (h g) = H g`.
- `IsNormalizingFunction`
- `quotientAverageENNReal`, `quotientAverageENNReal_mk`
- `isNormalizingFunction_count_iff`
- `IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal`
- `IsNormalizingFunction.ae_lt_top`
- `IsCompatible.lintegral_descend_eq`
- `IsCompatible.eq_map_withDensity`
- `IsCompatible.lintegral_eq_lintegral_mul_comp`
- `IsCompatible.integrable_iff_integrable_smul_comp`
- `IsCompatible.integral_eq_integral_smul_comp`
- `measurable_descend`
- `IsCompatible.integrable_descend_iff`
- `IsCompatible.integral_descend_eq`
- `IsCompatible.lintegral_mul_eq_of_isNormalizingFunction`
- `IsCompatible.integral_smul_eq_of_isNormalizingFunction`
- `exists_bump` (private): the function `β` of the existence proof.
- `exists_continuous_isNormalizingFunction`

## Literature

G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition (2015), §2.6, written for
the space `G/H` of cosets `x H` (here the mirror image `H \ G`):

- (2.47), printed p. 61: the fiber integral `P f (xH) = ∫_H f (x ξ) dξ`; p. 69, before Lemma 2.66,
  the remark that `P f` makes sense for every Borel measurable `f : G → [0, ∞]`
  (`quotientAverageENNReal`).
- Theorem 2.51 and formula (2.52), printed p. 62: Weil's formula `∫_G f = ∫_{G/H} P f dμ` for
  `f ∈ C_c(G)` when the quotient measure exists.
- Lemma 2.55, printed pp. 64–65: a continuous `f ≥ 0` on `G` whose positivity set meets every coset
  and whose support meets `K H` in a compact set for every compact `K`. Folland's proof uses a maximal
  family of translates (Lemma 2.54, Zorn's lemma) and needs no countability; the proof here uses a
  compact exhaustion and therefore assumes `G` σ-compact.
- Lemma 2.66, printed p. 69: formula (2.59), `∫ P f dμ = ∫ f ρ`, for lower semicontinuous `f ≥ 0`.

N. Bourbaki, *Intégration, chapitres 7 et 8* (1963), Chapter VII, §2, written for a locally compact
group `H` acting on the right, continuously and properly, on a locally compact space `X`, with a left
Haar measure `β` on `H` and `f^b(ẋ) = ∫_H f(x ξ) dβ(ξ)` on `X/H` (here the mirror image: `H` acts on
`G` on the left, `μH` is right invariant, and the cosets are `H g`):

- no. 2, formula (3), printed p. 42, and Proposition 4, formula (6), with Definition 1 and formula
  (7), printed pp. 43–44: the quotient `λ = μ/β` of a measure `μ` on `X` (and `μ = λ#`), determined by
  `∫_X f dμ = ∫_{X/H} f^b dλ` for compactly supported continuous `f`; this is what `IsCompatible`
  asks of `ν`.
- no. 3, Proposition 5 b), printed p. 46: for `f ≥ 0` measurable and vanishing outside a countable
  union of integrable sets, `∫* f dλ# = ∫* dλ(ẋ) ∫* f(x ξ) dβ(ξ)`
  (`IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal`; here the countability condition is
  automatic, the measures being σ-finite).
- no. 4, Proposition 8, printed p. 51: if `X/H` is paracompact, there is a continuous `h ≥ 0` on `X`
  whose support meets the saturation of every compact set in a compact set, with `h^b = 1`
  (`exists_continuous_isNormalizingFunction`, which states the support property for the points where
  `ρ` does not vanish and assumes `G` σ-compact instead of the quotient paracompact). Remark 1, same
  page: for a discrete group `D`, `Σ_{d ∈ D} h(x d) = 1` (the condition of
  `isNormalizingFunction_count_iff`).
- no. 4, Proposition 9, printed pp. 51–52, for `h` as in Proposition 8 and a positive measure `λ` on
  `X/H`: the projection `π` is proper for `h · λ#` and `π(h · λ#) = λ` (b), p. 51; this is
  `IsCompatible.eq_map_withDensity`), and a function `k` on `X/H` is measurable, integrable, … for
  `λ` exactly when `h · (k ∘ π)` is for `λ#`, with `∫ k dλ = ∫ h · (k ∘ π) dλ#`, formula (14)
  (c), p. 52; this is `IsCompatible.integrable_iff_integrable_smul_comp` and
  `IsCompatible.integral_eq_integral_smul_comp`). Bourbaki uses the continuous `h` of Proposition 8;
  the rule here holds for every measurable normalizing `ρ`.

## Source and licence

Port, in part, of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

- `exists_bump` and `exists_continuous_isNormalizingFunction` are ported from
  `src/Development/AutomorphicArithmetic/Foundations/Convolution/LocalGroupAnalysis/ClosedSubgroupCutoffExists.lean`,
  lines 8–157 (`exists_bump`, `closedSubgroup_cutoff_exists`, the proof of the source's statement
  `PositivityTheory.Rg.Tf.Geo.Q2`). Changes: the closed embedding `i : T →* X` of the source is
  replaced by a closed subgroup `H : Subgroup G` with its subtype; second countability and the Haar
  hypotheses on `T` are replaced by σ-compactness of `G` and, on `μH`, right invariance, finiteness on
  compacts and positivity on open sets; the continuity of `D` is proved with
  `continuousOn_integral_of_compact_support` (no first countability) in place of
  `continuous_parametric_integral_of_continuous`; the source's `IsNormAlong` becomes
  `IsNormalizingFunction`; names, universes and docstrings are the Library's.
- `IsNormalizingFunction` restates the source's predicates `IsNormAlong`
  (`src/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/SelmerRankBounds/IsNormAlong.lean`,
  lines 21–22) and `IsQuotNormaliser`
  (`src/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean`,
  lines 105–106) for a subgroup.
- The rule (`IsCompatible.lintegral_descend_eq`, `IsCompatible.integral_descend_eq`) has the content
  of the source's statement `Q1` (`…/SelmerRankBounds/EllipticityFromProductFormula.lean`, lines 77–83),
  but its proof is new: the source compares two normalizing functions by Fubini
  (`LintegralOfRealToReal.lean`, `LintegralSwapNorm.lean`) inside its integral `quotInt` defined by
  choice; here the rule is derived from the Library's Weil formula `lintegral_orbitKernel`, and no
  integral is defined by choice.
