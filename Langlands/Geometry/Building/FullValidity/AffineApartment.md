# Axiom 4.1.4: the affine structure on the apartments

This module states KP Axiom 4.1.4, the affine structure on the apartments, for the Library's
valuation building data. It is part of the full corrected Definition 4.1.26 predicate (task
`129deca1-ce21-411b-9b79-7e94545fe26d`). It contains supplied data for the derived torus and the
split central torus, one structure of validity clauses, and lemmas derived from these clauses.
The lemmas compare KP's translation space `V(S')` with the Library's translation space and
prove (A 2) for every building datum. Nothing here asserts that the clauses hold for given data,
or that data exist.

Ambient setting: as in `Langlands.Geometry.Building.FullValidity.Realization`. `F` is a
nonarchimedean local field in universe `u`, `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`, and `B : ValuationBuildingData G` has maximal split torus `i : S → G`
(`B.i`), normalizer points `N(F) = normalizerPoints B.i`, centralizer datum `Z = B.centralizer.Z`
and apartment `A(S) = B.Apartment`.

Source: T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Axiom 4.1.4 is on PDF 189–190 (printed
pp. 158–159). The 2024 corrections (`kaletha-prasad-2024-corrections`) do not change it.

## The translation space: Library form and KP form

In the Library, `A(S)` is an affine space under `TranslationSpace B.i = V(S)/V(S)^Φ`, where
`V(S) = ℝ ⊗ X_*(S)` and `V(S)^Φ = rootAnnihilator B.i` is the common kernel of the relative roots.
`N(F)` acts through `B.normalizerAction : normalizerPoints B.i →* (A(S) ≃ᵃ[ℝ] A(S))`, whose
derivative is the action on `V(S)` (`ValuationBuildingData.normalizerAction_linear`).
`z ∈ Z(F)` acts by the translation by the class of `ν(z) = -ω_Z(z)`
(`ValuationBuildingData.translation`, `normalizerAction_centralizer`). KP instead uses
`V' = V(S')`, where `S'` is the maximal subtorus of `S` in `G_der`, through the canonical
decomposition `V(S) = V(S') ⊕ V(A_G)`. This module supplies `S'` and `A_G` as actual data. It
then builds the explicit comparison `derivedTranslationEquiv : V(S') ≃ₗ[ℝ] TranslationSpace B.i`,
`v ↦ [e(v)]`, and transports each clause of (A 1) and (A 2) along it. The objective allows this
form ("an explicitly compared equivalent space").

## Supplied data and validity clauses

Supplied data: `T : B.ApartmentSplitting`, a structure with fields

* `D : GroupScheme (Spec F)` and `d : D ⟶ G`, meant to be the derived subgroup `G_der`;
* `derivedTorus : CommGroupScheme (Spec F)` with `j : derivedTorus.toGrp ⟶ D` and
  `e : derivedTorus ⟶ B.S`, meant to be `S'`;
* `centralTorus : CommGroupScheme (Spec F)` with `a : centralTorus ⟶ B.S`, meant to be `A_G`.

Validity clauses: `B.SatisfiesAffineApartmentAxiom T`, a structure with nine fields, and the
predicate `B.HasAffineConjugations`.

## Map of Axiom 4.1.4

| Source (KP Axiom 4.1.4) | Lean |
|---|---|
| Preamble, PDF 189 (p. 158): "Let `S'` be the unique maximal subtorus of `S` that is contained in the derived subgroup `G_der` of `G`." | Fields `isDerivedSubgroup : IsDerivedSubgroup T.d`, `isMaximalSplitTorus_j : IsMaximalSplitTorus T.j`, `isClosedSubgroup_e : IsClosedSubgroup (groupHom T.e)` and `j_comp_d : T.j ≫ T.d = groupHom T.e ≫ B.i`. So `S'` is a subtorus of `S` lying in `G_der` that is a maximal split torus of `G_der`. Any subtorus of `S` in `G_der` generates with `S'` a split torus of `G_der` containing `S'`, so it lies in `S'`. Hence these clauses single out KP's `S'` (a mathematical remark, not formalized). Existence of such `S'` is the content of `Langlands.GroupScheme.DerivedMaximalSplitTorusStatement` (proof task `45bba50f-b29d-49c2-b923-64037208e2e1`). |
| Preamble: "`V(S) = ℝ ⊗ X_*(S)` and `V(S') = ℝ ⊗ X_*(S')`." | The Library's real cocharacter spaces `V B.S` and `V T.derivedTorus`. The maps `V(S') → V(S)` and `V(A_G) → V(S)` are `cocharacterMapReal T.e` and `cocharacterMapReal T.a`. |
| Preamble: "`A_G` is the maximal `k`-split torus in the center of `G`." | Field `isSplitComponent : IsSplitComponent (groupHom T.a ≫ B.i)`. This is the Library's split component (`Langlands.GroupScheme.Rational.Characters`): `a ≫ i` is a central split torus, and whenever it factors as `f ≫ i'` through a central split torus `i' : A' → G`, the map `f : A_G → A'` is an isomorphism. So `A_G` has no proper enlargement among the central split tori of `G`, which is KP's maximality. The condition says nothing about maps from smaller central split tori into `A_G`. |
| Preamble: "`S' → S → S/A_G` is an isogeny, hence … a canonical decomposition `V(S) = V(S') ⊕ V(A_G)`." | Field `isCompl : IsCompl (range (cocharacterMapReal T.e)) (range (cocharacterMapReal T.a))`. KP derives it from the isogeny `S' × A_G → S`. The Library does not prove that generic split-torus fact. Worker 1107's algebraic program owns it (see the task context), so it is a validity clause here. `injective_cocharacterMapReal_e` gives `V(S') ↪ V(S)` from the closed immersion `e` (`mono_e`). `derivedProjection` is the projection `V(S) → V(S')` along `V(A_G)`, with `derivedProjection_e` and `derivedProjection_a`. |
| A 0, PDF 189: "`A` is equipped with the structure of an affine space under `V' = V(S')`." | `B.Apartment` is an affine space under `TranslationSpace B.i`. The theorem `range_cocharacterMapReal_a` proves `V(A_G) = V(S)^Φ` from `isSplitComponent` and the Library's proved `rootAnnihilatorCentrality`. `isCompl_rootAnnihilator` then shows that `V(S)^Φ` is a complement of `V(S')`. `derivedTranslationEquiv : V T.derivedTorus ≃ₗ[ℝ] TranslationSpace B.i`, `v ↦ [e(v)]` (`derivedTranslationEquiv_apply`), makes `A(S)` an affine space under `V(S')`. `derivedTranslationEquiv_derivedProjection` gives `[v] = derivedTranslationEquiv (derivedProjection v)`, so it inverts the canonical splitting. |
| A 1, PDF 190 (p. 159): "The action of `N(k)` on `A` is by affine transformations." | Built into `B` as `B.normalizerAction`. |
| A 1: "the derivative `df(n) ∈ Aut(V')` is the automorphism of `V'` induced by the action of `N(k)` on `X_*(S')`." | Field `normalizer_derivedTorus`: for each `n ∈ N(F)` there is `τ : S' ≅ S'` with `τ ≫ e = e ≫ Int(n)|_S` (`normalizingAut B.i n`). So `N(F)` preserves `S'`, and this is how it acts on `X_*(S')`. Theorem `linear_normalizerAction_derivedTranslationEquiv` shows that the derivative of `B.normalizerAction n`, read through `derivedTranslationEquiv`, is `cocharacterRealAut τ`, the action on `V(S') = ℝ ⊗ X_*(S')`. |
| A 1: "`Z(k)` acts on `A` by translations, where the translation `ν(z) ∈ V'` … is the image under `V(S) → V(S')` of `-ω_Z(z)`." | `derivedTranslation z := derivedProjection (B.translation z)`, the projection to `V(S')` of the Library's `ν(z) = -ω_Z(z) ∈ V(S)`. Theorem `normalizerAction_centralizer_eq_constVAdd_derivedTranslation` shows that `z` acts as the translation by `derivedTranslationEquiv (derivedTranslation z)`. |
| A 1: "In particular, the maximal bounded subgroup `Z(k)_b` of `Z(k)`, and the center `Z_G(k)`, act trivially." | Field `center_acts_trivially`: every `n ∈ N(F)` lying in the centre's points `(center G).carrier (Over.mk (𝟙 _))` acts as the identity. For `Z(k)_b`, the Library proves that `Z(F)^1 = ker ω_Z` acts trivially (`KPCentralizerCompatibility`). A bounded subgroup of `Z(F)` has bounded character values, so it lies in `Z(F)^1`. That comparison is not formalized here and is not a separate clause. |
| A 1: "For convenience, we note here that `a(ν(s)) = -ω(a(s))`." | A remark about the Library's `ν`, not an axiom. No clause. |
| A 2, PDF 190: "For any `g ∈ G(k)`, the isomorphism `g : A(S) → A(gSg⁻¹)` is affine and its derivative is the natural isomorphism `g : V(S') → V(gS'g⁻¹)`." | `B.HasAffineConjugations` (field `affineConjugations`), explained below. The theorem `hasAffineConjugations` proves it for every `B`. `exists_derivedConjugation` gives the derivative on `V(S')`. |

## Axiom 4.1.4 (A 2) on actual tori

`HasAffineConjugations` quantifies over actual maximal split tori and all their charts:

* tori `i₂ : T₂ → G`, `i₃ : T₃ → G`, a point `g ∈ G(F)` and an isomorphism `σ : T₂ ≅ T₃` with
  `i₂ ≫ Int(g) = σ ≫ i₃`, so that `T₃ = g T₂ g⁻¹` with its natural identification;
* charts `(h₂, σ₂)` of `T₂` and `(h₃, σ₃)` of `T₃` (`IsTorusChart` from the realization module).
  These read the apartments `A(T₂) = h₂ · A(S)` and `A(T₃) = h₃ · A(S)` through
  `x ↦ B.translatedApartmentMap h x = h · x`. That these are the apartments of `T₂` and `T₃` is
  `HasTorusApartmentCorrespondence.torusApartment_range` under Axiom 4.1.1.

The conclusion is that there is an affine automorphism `f` of `A(S)` with
`g · (h₂ · x) = h₃ · f(x)`. Its derivative on `TranslationSpace B.i` is induced by
`V(σ₂ ≫ σ ≫ σ₃⁻¹)` on `V(S)`, which is the natural isomorphism `V(T₂) → V(T₃)` in the charts.

All charts are allowed, so the clause includes independence of the chart.
`exists_chartTransition` is the case `g = 1`: two charts of the same torus differ by an affine
automorphism with derivative `V(σ ≫ σ'⁻¹)`.

Why it always holds (`hasAffineConjugations`): `isNormalizingPoint_conjugation` shows that
`h₃⁻¹ g h₂` normalizes `S` through the automorphism `σ₂ ≫ σ ≫ σ₃⁻¹`. So `f` is the normalizer
action of `h₃⁻¹ g h₂`, whose derivative is given by `normalizerAction_linear` together with
uniqueness of the normalizing automorphism (`IsNormalizingPoint.unique`). This uses that the
apartments of `B(G)` are the translates `h · A(S)`, as in KP §7.6. The field `affineConjugations`
is therefore redundant. It is kept so that the clause list shows every sentence of the axiom.

The derivative on `V(S')`: `SatisfiesAffineApartmentAxiom.exists_derivedConjugation` gives the
same `f` with derivative `V(τ')` on `V(S')` (through `derivedTranslationEquiv`), where `τ'` is the
restriction of `σ₂ ≫ σ ≫ σ₃⁻¹` to `S'`. This is the natural isomorphism
`V(T₂') → V(T₃')` between the derived subtori `T₂' = σ₂(S')` and `T₃' = σ₃(S')`. The supporting
lemmas are `quotientMk_cocharacterRealAut_e` and `linear_derivedTranslationEquiv`.

## Interfaces to existing objects

* The apartment, its affine structure and the `N(F)`- and `Z(F)`-actions are the Library's
  `ValuationBuildingData` objects, used unchanged. The chart transitions of
  `Langlands.Geometry.Building.ValuationBuildingApartmentCharts` (`translatedApartmentMap`) are
  used in (A 2).
* `S'`, `G_der` and `A_G` are actual group schemes with the Library predicates
  `IsDerivedSubgroup`, `IsMaximalSplitTorus`, `IsClosedSubgroup` and `IsSplitComponent`.
* `rootAnnihilatorCentrality` (Library, proved) identifies `V(A_G)` with `V(S)^Φ`.
* The Library's published `adjointRealCocharacterComparison` (`TranslationSpace i ≃ₗ[ℝ] V(T_ad)`)
  gives a second, adjoint form of the translation space. That form fits the `G_ad` comparison of
  Axiom 4.1.1 and is not needed here.
