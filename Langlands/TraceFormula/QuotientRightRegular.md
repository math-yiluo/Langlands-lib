# The right regular representation on `L²(Γ \ G)`

Module `Langlands.TraceFormula.QuotientRightRegular`, namespace `Langlands.TraceFormula`.

Let `G` be a topological group, `Γ` a subgroup, `LeftQuotient Γ` the space of cosets `Γ x`
with the quotient topology, and `ν` a measure on it (for a supplied measurable structure).
Assume `hν : ∀ g, MeasurePreserving (rightTranslate Γ g) ν ν`, where `rightTranslate Γ g` is
`Γ x ↦ Γ x g` (`Langlands/Group/LeftQuotient.lean`). The module builds the right regular
representation of `G` on `L²(Γ \ G, ν)` and proves the properties that the Library's abstract
simple twisted trace formula (`AbstractSimpleTwistedTraceFormulaStatement`) and the comparison
of the positive and norm-one quotients (`PositiveQuotientTraceComparisonStatement`) ask of a
representation.

## Declarations

- `continuous_rightTranslate_uncurry Γ`: the map `(g, Γ x) ↦ Γ x g` on `G × LeftQuotient Γ` is
  continuous. The proof composes with the product of the identity and the open quotient map
  `G → LeftQuotient Γ` (`leftQuotient_isOpenQuotientMap`), which is again an open quotient
  map, so continuity reduces to that of `(g, x) ↦ Γ x g` on `G × G`.
- `quotientRightTranslateL2 Γ ν hν g : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν`: composition with
  `rightTranslate Γ g`, the continuous linear map underlying Mathlib's linear isometry
  `Lp.compMeasurePreservingₗᵢ`.
- `quotientRightRegular Γ ν hν : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)`, with
  `quotientRightRegular Γ ν hν g = quotientRightTranslateL2 Γ ν hν g`. It is a monoid
  homomorphism: `R(1) = 1` because `rightTranslate Γ 1` is the identity, and
  `R(g h) = R(g) ∘ R(h)` because `rightTranslate Γ h (rightTranslate Γ g q) =
  rightTranslate Γ (g * h) q`. Both identities are proved almost everywhere from
  `Lp.coeFn_compMeasurePreserving`, using that a measure-preserving map is
  quasi-measure-preserving.
- `quotientRightRegular_apply`: `R(g) φ = Lp.compMeasurePreserving (rightTranslate Γ g) (hν g) φ`
  (definitional).
- `norm_quotientRightRegular_apply`: `‖R(g) φ‖ = ‖φ‖` (`Lp.norm_compMeasurePreserving`).
- `quotientRightRegular_coeFn`: `R(g) φ =ᵐ[ν] fun q => φ (rightTranslate Γ g q)`.
- `continuous_quotientRightRegular_apply`: if moreover `LeftQuotient Γ` carries the Borel
  structure and is `R₁`, and `ν` is inner regular for sets of finite measure
  (`InnerRegularCompactLTTop`, implied by `Regular`) and locally finite, then `g ↦ R(g) φ` is
  continuous. The proof applies Mathlib's `Continuous.compMeasurePreservingLp` to the
  constant map `φ` and to the continuous map `G → C(LeftQuotient Γ, LeftQuotient Γ)` obtained by
  currying `continuous_rightTranslate_uncurry`.
- `aestronglyMeasurable_quotientRightRegular_apply`: under the same hypotheses, and if `G` is
  second countable with an opens-measurable structure, `g ↦ R(g) φ` is almost everywhere
  strongly measurable for every measure on `G`, by continuity.

## Origin

This is the right regular representation `R` whose integrated operators `R(f)` appear in the
simple trace formula (Getz–Hahn, *An Introduction to Automorphic Representations*, 2024,
registered `getz-hahn-2024-automorphic-representations`, Corollary 18.4.1, printed p. 485). The
construction is the standard one; the module's content is the verification, for the Library's
coset spaces and measures, of the hypotheses used by the Library's trace formula statements.
`Langlands.Automorphic.GroupSchemeFunctions.haarQuotientL2JointRightAction`
(`Langlands/Automorphic/GroupSchemeQuotientL2Continuity.lean`) proves the analogous continuity
for the positive quotient of a group scheme by the same Mathlib lemma.

For the norm-one quotient `Γ \ G(𝔸_F)¹` of a group scheme over a number field, `hν` is the field
`right_invariant` of `normOneRationalQuotientHaarMeasure_isCompatible`, and the instance
hypotheses of the continuity lemma hold by the Library's instances
`normOneRationalQuotientBorelSpace`, `normOneRationalQuotientT2Space`,
`normOneRationalQuotientHaarMeasure_regular` and
`normOneRationalQuotientHaarMeasure_isLocallyFiniteMeasure`; this is how
`Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof` uses the module.
