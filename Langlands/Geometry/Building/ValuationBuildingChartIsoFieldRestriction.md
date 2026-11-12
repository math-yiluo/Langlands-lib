# Field restriction of apartment data as a chart isomorphism

This is an internal coherence unit toward Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms) for the valuation-quotient buildings of
supplied `ValuationBuildingData`. It does not prove that axiom. It shows that
the published literal field restriction of apartment data
(`KPApartmentData.fieldRestrict`, module `RootApartmentFieldDescent`) is a chart
isomorphism in the sense of `KPApartmentData.IsChartIso`
(module `ValuationBuildingChartIso`) whenever the rational-point extension
`rationalExtend k K G : G(k) → G(K)` is bijective and reflects the normalizer of
the torus. The intended use is a field isomorphism `σ : F₁ ≃+* F₂`, viewed as
the algebra `F₁ → F₂`. Bijectivity of `rationalExtend` is not automatic for a
general field extension. Normalizer reflection does hold for an arbitrary field
extension (by faithfully flat descent of the conjugacy witness); this API
nevertheless keeps it as an explicit hypothesis `hN`.

## Provenance

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axiom 4.1.17, printed p.162 (PDF p.193), read with the authors'
corrections of 1 November 2024 (PDF p.27). Registered source IDs:
`kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The declarations are derived from the
published field-restriction API: `fieldRestrict`, `fieldRestrictAffineEquiv`,
`fieldExtendPoint`, `fieldExtendPoint_normalizer`, `filtration_fieldExtendPoint`
(`RootApartmentFieldDescent`, `RootBuildingFieldExtension`),
`fieldExtendAffineFunctional`, `fieldExtendAffineFunctional_linear`,
`affineRootGroup_fieldRestrict`, `affineRootGroupPlus_fieldRestrict`
(`RootAffineFieldRestriction`), `rootsBaseChangeEquiv`,
`mem_roots_baseChange_iff` (`RootSupportBaseChange`),
`rationalExtend_mem_rootGroupPoints_iff` (`RootFunctionFieldRestriction`) and
`rootForm_splitTranslationBaseChange`. They are not statements from the source.

## Setting

`k → K` is a field extension, `G` an affine smooth group scheme over `k`,
`i : S → G` with `S` split (`hS`), `hE` the opposite factor pairs of `i`,
`ω : Kˣ →* Multiplicative ℝ` with `hω` (a unit of `k` of nonzero order), and
`D` apartment data for the base change `i_K` with field order `(ω ·).toAdd`.
`hθ` is bijectivity of `rationalExtend k K G`.

## Group-theoretic helpers

- `coe_comap_subset_mul_iff`: for a bijective homomorphism `f` and subgroups
  `A`, `B`, `C`, `f⁻¹A ⊆ f⁻¹B · f⁻¹C` (as sets) if and only if `A ⊆ B · C`.
- `comap_iSup_of_bijective`: preimages along a bijective homomorphism commute
  with suprema of subgroups (rewrite the preimage as the image under the
  inverse `MulEquiv`, then `Subgroup.map_iSup`).

## Comparison results (assuming `hθ`)

- `sharpFixer_fieldRestrict_eq`: the sharp fixer of a restricted point `x` is
  the preimage under `rationalExtend` of the upstairs sharp fixer at
  `fieldExtendPoint x`. Both are suprema of root fixers; root fixers at a point
  are filtrations (`rootFixer_singleton`), which correspond by
  `filtration_fieldExtendPoint`; the roots correspond by the bijection
  `rootsBaseChangeEquiv`.
- `doubleRootGroupPoints_eq_comap`: the double root group `U_{2a}(k)` (or `⊥`)
  is the preimage of `U_{2a_K}(K)` (or `⊥`). Doubling commutes with the
  additive character base change, `2a` is a root exactly when `2a_K` is
  (`mem_roots_baseChange_iff`), root groups are preimages
  (`rationalExtend_mem_rootGroupPoints_iff`), and `⊥` is the preimage of `⊥`
  by injectivity.
- `fieldExtendAffineFunctional_linear_iff` (no `hθ` needed): the extended
  functional has derivative the base-changed root form exactly when the
  original has the root form; the converse of the published
  `fieldExtendAffineFunctional_linear` evaluates at
  `splitTranslationBaseChange w` and uses `rootForm_splitTranslationBaseChange`.
- `fieldExtendAffineFunctional_mem_affineRoots_iff`: `ψ` is an affine root of
  the restricted data (KP Definition 6.3.4: derivative a root `a` and
  `U_ψ ⊈ U_{ψ+} · U_{2a}`) exactly when its extension is an affine root
  upstairs. The three subgroups downstairs are preimages of those upstairs
  (`affineRootGroup_fieldRestrict`, `affineRootGroupPlus_fieldRestrict`,
  `doubleRootGroupPoints_eq_comap`), so `coe_comap_subset_mul_iff` applies.
- `transportedRoots_fieldRestrict`: transport along the inverse restriction
  equivalence `(fieldRestrictAffineEquiv …).symm` carries the affine roots of
  the restricted data onto those of `D`.

## The chart isomorphism

- `rationalExtendEquiv hθ : G(k) ≃* G(K)` is `MulEquiv.ofBijective` of
  `rationalExtend`; `rationalExtendEquiv_apply` and
  `rationalExtendEquiv_toMonoidHom` identify it with `rationalExtend`.
- `mem_sharpFixer_fieldRestrictAffineEquiv_symm_iff` restates
  `sharpFixer_fieldRestrict_eq` pointwise.
- `fieldRestrictBuildingEquiv hθ hN D` is the published
  `KPApartmentData.congrBuildingEquiv` for `rationalExtendEquiv hθ`, the inverse
  restriction equivalence, the normalizer hypothesis
  `hN : ∀ g, rationalExtend g ∈ N(i_K)(K) ↔ g ∈ N(i)(k)`, the published
  normalizer compatibility `fieldExtendPoint_normalizer`, and the sharp-fixer
  comparison. It sends `[(g, x)]` to `[(g_K, x_K)]`.
- `isChartIso_fieldRestrictBuildingEquiv`: this equivalence is a chart
  isomorphism from `fieldRestrict … D` to `D` along `rationalExtend k K G`,
  with base point `1` and apartment map `(fieldRestrictAffineEquiv …).symm`,
  by `isChartIso_congrBuildingEquiv` and `transportedRoots_fieldRestrict`.

The bijectivity and normalizer hypotheses are explicit; no building axiom,
V 7, AS 5 or availability hypothesis is used.
