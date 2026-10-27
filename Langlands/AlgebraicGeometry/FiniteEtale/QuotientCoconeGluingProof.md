# Finite-étale group quotient cocones over arbitrary locally noetherian bases

The theorem `Langlands.AlgebraicGeometry.FiniteEtale.finiteGroupQuotientCocones` proves the
published proposition `FiniteGroupQuotientCocones` from
`Langlands.AlgebraicGeometry.FiniteEtale.QuotientCoconeStatements`:

```lean
theorem finiteGroupQuotientCocones : FiniteGroupQuotientCocones.{u}
```

The statement is used unchanged. It quantifies over the universe `u`, an arbitrary locally
noetherian base `S`, an arbitrary finite group `G`, and an arbitrary diagram
`D : SingleObj G ⥤ Cover S`. There are no extra hypotheses. The base need not be affine or
connected, the action need not be free or faithful, and `|G|` need not be invertible.

The cocone is the scheme glued from the spectra of invariant sections over the affine opens of
`S`, built in the helper module `QuotientGluingConstruction` (see its Markdown). That module
supplies `gluedQuotient D`, the finite étale structure morphism `gluedStructure D`, the open
cover `gluedCover D` by the charts `Spec (invariantRing D U)`, and the invariant quotient map
`gluedMap D`. The helper declarations below live in
`Langlands.AlgebraicGeometry.FiniteEtale.QuotientGluing`. The module sets
`backward.isDefEq.respectTransparency false`, as `Definitions` does.

## Points in the range of an open immersion

Take an open immersion `j : Spec A ⟶ Z` and a map `x : Spec K ⟶ Z` with
`Set.range x ⊆ Set.range j`. Then `pointRing j x h : A ⟶ K` is
`Spec.preimage (IsOpenImmersion.lift j x h)`. `SpecMap_pointRing_comp` gives
`Spec.map (pointRing j x h) ≫ j = x`. `pointRing_eq` says any `φ` with `Spec.map φ ≫ j = x`
equals `pointRing j x h`.

## Descending invariant maps

Fix `t : Z ⟶ S` and `ψ : coverScheme D ⟶ Z` with `hψ : ψ ≫ t = coverHom D` and
`hinv : ∀ g, coverMap D g ≫ ψ = ψ`.

- For each open `U` of `S`, `descRing D ψ hψ hinv U : Γ(Z, t ⁻¹ᵁ U) ⟶ invariantRing D U` is the
  codomain restriction of `ψ.appLE`. Its image is invariant by `hinv`.
  `descRing_comp_invariantInclusion` recovers `ψ.appLE`. `appLE_comp_descRing` shows that
  `descRing` is compatible with the structure maps from `Γ(S, U)`.
- Assume `[Finite G]` and `[IsAffineHom t]`. Then `gluedDesc D ψ hψ hinv : gluedQuotient D ⟶ Z`
  is `colimit.desc` of the gluing diagram. On the chart of an affine open `U` it is
  `Spec.map (descRing D ψ hψ hinv U) ≫ (U.preimage t).fromSpec`; the preimage `t ⁻¹ᵁ U` is
  affine because `t` is affine. Naturality reduces, as in Mathlib's `normalizationDesc`, to
  `IsAffineOpen.map_fromSpec` and the compatibility of `appLE` with restriction.
  `gluedCover_f_gluedDesc` records the value on each chart.
- `gluedMap_gluedDesc` gives `gluedMap D ≫ gluedDesc D ψ hψ hinv = ψ`. It is checked on every
  `(U.preimage (coverHom D)).fromSpec` with `coverScheme_hom_ext`, using `fromSpec_gluedMap` and
  `IsAffineOpen.SpecMap_appLE_fromSpec`.
- `gluedDesc_comp` gives `gluedDesc D ψ hψ hinv ≫ t = gluedStructure D`, checked chart by chart
  with `appLE_comp_descRing`.
- `gluedQuotient_hom_ext` is uniqueness. If `m₁ m₂ : gluedQuotient D ⟶ Z` both lie over `S`
  through `t` and `gluedMap D ≫ m₁ = gluedMap D ≫ m₂`, then `m₁ = m₂`. On each chart both maps
  send `Spec (invariantRing D U)` into the affine open `t ⁻¹ᵁ U`. Mathlib's lemma
  `eq_of_SpecMap_comp_eq_of_isAffineOpen` (in `AlgebraicGeometry.AffineScheme`), applied with the
  injective `invariantInclusion D U`, reduces equality to equality after composing with
  `Spec.map (invariantInclusion D U)`. That follows from `fromSpec_gluedMap` and the hypothesis.

## The glued quotient cocone

Assume `[IsLocallyNoetherian S] [Finite G]`, so that `gluedStructure D` is finite étale.

- `gluedQuotientCover D := cover (gluedStructure D)` is the vertex in `Cover S`.
- `gluedCoconeMap D` is the cover morphism with underlying map `gluedMap D`, over `S` by
  `gluedMap_gluedStructure`.
- `gluedCocone D : Cocone D` has this leg at the unique object. Naturality is
  `coverMap_gluedMap`.
- `gluedCoconeIsColimit D : IsColimit (gluedCocone D)`. For a cocone `s`, the descended map has
  underlying morphism `gluedDesc` applied to the leg of `s`. That leg is invariant by the Library
  lemma `cocone_leg_invariant`. The structure morphism of `s.pt` is finite, hence affine.
  `gluedDesc_comp` makes the descended map a morphism over `S`. Factorization is
  `gluedMap_gluedDesc`, and uniqueness is `gluedQuotient_hom_ext`.

The universal property is proved in the actual category `Cover S`, against every cocone.

## Geometric points

Fix `Ω : Type u` with `[Field Ω]`, a point `s : Spec (.of Ω) ⟶ S`, and an affine open `U` with
`hs : ∀ p, s p ∈ U`. `exists_affine_mem` provides such a `U`: `Spec Ω` has one point, and the
affine opens cover `S`.

- `baseRing s U hs : Γ(S, U) ⟶ Ω` is the ring map of `s` through `U.fromSpec`
  (`range_subset_fromSpec`).
- `coverPointRing D s U hs x : Γ(coverScheme D, coverHom D ⁻¹ᵁ U) ⟶ Ω` is the ring map of a
  geometric point `x` of the cover, through `(U.preimage (coverHom D)).fromSpec`
  (`range_subset_fromSpec_preimage`).
  - It is injective (`coverPointRing_injective`) and compatible with `baseRing`
    (`app_comp_coverPointRing`).
  - Every ring map compatible with `baseRing` comes from a geometric point
    (`exists_coverPointRing`).
  - The action becomes precomposition (`coverPointRing_map`):
    `coverPointRing D s U hs ((pointFunctor s).map (D.map (SingleObj.toEnd G g)) x) = sectionAction D U g ≫ coverPointRing D s U hs x`.
- `quotientPointRing D s U hs y : invariantRing D U ⟶ Ω` is the ring map of a geometric point `y`
  of the glued quotient through the chart `(gluedCover D).f U`. The range condition is
  `range_subset_gluedCover`, which uses `gluedStructure_preimage`.
  - It is injective (`quotientPointRing_injective`) and compatible with `baseRing`
    (`algebraMap_comp_quotientPointRing`).
  - `quotientPointRing_map` identifies the image of `x` under the cocone leg with
    `invariantInclusion D U ≫ coverPointRing D s U hs x`.

Now assume `[IsAlgClosed Ω]`. Make `Ω` a `Γ(S, U)`-algebra through `baseRing s U hs`. Since
`Γ(S, U)` is noetherian and `sectionRing D U` is a finite étale `Γ(S, U)`-algebra
(`sectionRing_finite`, `sectionRing_etale`), the Library theorem
`invariantAlgebraGeometricPoints Γ(S, U) (sectionRing D U) G Ω` applies.

- `gluedCocone_surjective`: a point `y` of the quotient gives the algebra map
  `quotientPointRing D s U hs y` from the invariants. Its surjectivity part lifts this map to
  `sectionRing D U`. `exists_coverPointRing` turns the lift into a geometric point `x`, and
  injectivity of `quotientPointRing` shows that `x` maps to `y`.
- `gluedCocone_orbit`: if two points `x` and `y` have the same image, their algebra maps agree on
  invariants. The orbit part gives `g` with `F y = (F x).comp (MulSemiringAction.toAlgHom _ _ g)`.
  Since `g` acts through `sectionAction D U g⁻¹`, `coverPointRing_map` and injectivity identify
  `y` with the image of `x` under `g⁻¹`. Conversely, translates have the same image by
  `invariantInclusion_comp_sectionAction`.

## The final theorem

`finiteGroupQuotientCocones` takes `S`, `G` and `D` and returns `gluedCocone D` together with
`⟨gluedCoconeIsColimit D⟩`. For each geometric point `s` it chooses `U` with
`exists_affine_mem` and supplies `gluedCocone_surjective` and `gluedCocone_orbit`. This is
exactly `FiniteGroupQuotientCocone D (gluedCocone D)`.

## Imports and provenance

The module imports only `QuotientGluingConstruction`, which imports the Library proofs
`AffineQuotientCoconeProof` and `InvariantAlgebraLocalizationProof`. Through them it uses
`invariantAlgebraFiniteEtale`, `invariantAlgebraGeometricPoints`, `invariantAlgebraLocalization`,
`coverScheme` and `cocone_leg_invariant`. Each chart of the glued
quotient is the affine invariant-spectrum quotient of the affine proof, formed for the sections
over the preimage of an affine open. The universal property and the orbit description are then
proved directly for the glued scheme; the module does not reuse the affine cocone itself.

The mathematics follows SGA 1, Exposé V, source `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`:

- Proposition 1.1 and Corollary 1.2, printed p.88, PDF p.104: the affine quotient, its orbit
  fibres, and its universal property.
- Proposition 1.8 and the following Corollary 1.8, printed p.90, PDF p.106: the quotient obtained
  by gluing affine quotients and defined by the sheaf of invariants.
- Corollary 3.4, printed p.97, PDF p.113: finite étaleness of the quotient.

The scheme-level arguments here are internal: the descent along the gluing, the uniqueness
argument, and the translation of geometric points into ring maps on an affine chart.
