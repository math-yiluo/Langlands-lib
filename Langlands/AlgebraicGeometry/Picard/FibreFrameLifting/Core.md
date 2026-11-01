# Spreading out the degree-zero restriction isomorphism over an affine base

Author: Worker 1119.

This module contains the affine-base core of the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`. It combines
`Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement` (B1) and
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (B2), both taken as
explicit hypotheses `h1`, `h2` of the main theorem, never as axioms. It contains no `sorry` and
no new axioms. The derived category instance is `HasDerivedCategory.standard`, the same local
instance as in B1.

## Auxiliary declarations

- `instPreservesFiniteLimitsRelativeGlobalSectionsOf`: left exactness of
  `relativeGlobalSections g` over a base `Spec (CommRingCat.of A)`. The general instance for
  `Spec R` is not found there. This mirrors the Library's additivity instance in
  `PerfectFibreVanishing`.
- `isIso_appTop_of_smoothProperConnected`: a smooth proper geometrically connected morphism is
  an isomorphism on global functions (the published `smoothProperConnectedGlobalFunctions` at
  `⊤`).
- `smoothProperConnected_of_isPullback`: these three properties pass to base changes
  (`MorphismProperty.of_isPullback`).
- `isIso_appTop_comp_of_isPullback`: if `g ≫ f` is smooth, proper and geometrically connected,
  `IsPullback p f' f t` and `IsPullback q j g p`, then `(j ≫ f').appTop` is an isomorphism
  (vertical pasting `IsPullback.paste_vert`).
- `nonempty_pullback_pullback_iso_unit`: if `d^* M ≅ 𝒪` and `a ≫ b = c ≫ d`, then
  `a^* b^* M ≅ 𝒪` (via `pullbackComp`, `pullbackCongr`, `pullbackUnitIso`).
- `nonempty_homology_zero_equiv`: let `M` be trivial on a closed piece `g : Y ⟶ X` with `g ≫ f`
  smooth, proper and geometrically connected. Let `K'` come with B1-style identifications `β`
  of `K' ⊗ T` with the derived sections of `g'_* g'^* p^* M`. Then for every ring map
  `φ : R →+* T`, `H⁰(K' ⊗ T) ≃ₗ[T] T`. Proof: take the squares `pullback f (Spec.map φ)` and
  `pullback g p`. Combine `DerivedPlus.homologyIsoOfIsoDerivedComplex` in degree `0`, `rightDerivedZeroIsoSelf`
  and `nonempty_relativeGlobalSections_pushforward_equiv`.

## Main result: `exists_spread_of_models`

Hypotheses: `f : X ⟶ Spec R` smooth, proper and geometrically connected, and
`L : LineBundle X`. Closed immersions `g₁, g₂` with each `gₖ ≫ f` smooth, proper and
geometrically connected, and `gₖ^* L ≅ 𝒪`. A field `k`, `φ₀ : R ⟶ CommRingCat.of k`, and a
fibre square `IsPullback ps fs f (Spec.map φ₀)` with closed fibre squares
`IsPullback qₖ jₖ gₖ ps`. Finally `ps^* L ≅ 𝒪`, and the units of `j₁, j₂` jointly detect zero
on `relativeCohomology fs 1` of `𝒪`, exactly as in the target statement.

Conclusion: there is `r : R` with `φ₀ r ≠ 0`, such that for every `φ : R ⟶ T` with `φ r` a
unit, every square `IsPullback p f' f (Spec.map φ)` and every square `IsPullback q g' g₁ p`,
the global sections of the unit `p^* L ⟶ g'_* g'^* p^* L` are bijective.

Proof. Apply `h1` to `f` and `L`, then to `g₁` and `g₂`. This gives strictly perfect `K, K₁, K₂`,
chain maps `ψₖ : K ⟶ Kₖ` and identifications `α`, `βₖ` compatible with the units. Apply `h2` to
`K, K₁, K₂, ψ₁, ψ₂` and `φ₀`. Its hypotheses are discharged as follows.

1. Negative cohomology of `K ⊗ k` and `Kₖ ⊗ k` vanishes (`isZero_homology_of_derivedIso` at the
   fibre squares).
2. `H⁰(Kₖ ⊗ T) ≃ₗ[T] T` for every `T` (`nonempty_homology_zero_equiv`).
3. `H⁰(ψ₁ ⊗ k)` is bijective. By the compatibility square of `h1`,
   `homologyMap_comp_homologyIsoOfDerivedIso` and `isIso_rightDerived_zero_map_iff`, this reduces
   to the global sections of the unit of `j₁` at `ps^* L`. That is an isomorphism by
   `isIso_map_unit_app_of_iso` (transport along `ps^* L ≅ 𝒪`) and
   `isIso_relativeGlobalSections_map_unit_unit` (`fs` and `j₁ ≫ fs` are smooth proper
   geometrically connected base changes, hence isomorphisms on global functions).
4. `H¹(ψ₁ ⊗ k)` and `H¹(ψ₂ ⊗ k)` jointly detect zero. `detectsZero_of_comm` is applied with
   the compatibility squares in degree `1` and the naturality of the units along `θ : ps^* L ≅ 𝒪`,
   reducing to the target's hypothesis `hH1`.

The resulting `r` is the one claimed. For `T`, `φ` and the two squares, `h2` gives bijectivity of
`H⁰(ψ₁ ⊗ T)`. The compatibility square of `h1` at these squares, `isIso_iff_of_comm` and
`isIso_rightDerived_zero_map_iff` transfer it to the global sections of the unit.

## Provenance

This is the algebraic heart of the proof of Stacks tag 0BF2 (`more-morphisms.tex`, lines
9543–9619, registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`), routed through B1 and B2. B1 packages the perfect
models and restriction maps compatible with base change. B2 packages the local minimal models,
the finite-matrix splitting and the vanishing of the differential. This module supplies the
degree-zero comparison with the structure sheaf and the identification of the degree-one
hypothesis. In the source, the degree-one hypothesis is injectivity of
`H¹(X_s, 𝒪) ⟶ ⊕ H¹(X_{k,s}, 𝒪)`. Here the target's unit form matches B1's unit form directly,
so no closed-immersion direct-image comparison is needed in this module: that comparison is
part of what B1's identifications `β` encode.
