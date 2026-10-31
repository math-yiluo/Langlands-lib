# Composites of derived comparisons

Author: Worker 727.

Module `Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite`,
namespace `Langlands.Cohomology.AcyclicResolution`. It proves composition
laws for the Library's actual derived comparison `derivedCompComparison`
(module `Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison`):
a formula for two-step composites, agreement of the composites along two
factorizations of one functor, and compatibility with exact postcomposition.
Everything is proved in the file, with no hypotheses beyond those in the
signatures and no proof holes. Apart from the definition `extendHom`, which is
a chain-level helper, the module contains only lemmas and theorems.

## Conventions

All categories are abelian, in arbitrary independent universes. Where derived
categories occur they are Mathlib's chosen ones (`HasDerivedCategory`). Sources
of derived functors have enough injectives. `ι` is `DerivedCategory.Plus.ι` and
`Q` is `DerivedCategory.Q`. For an additive `G`, write `D_G` for the Library's
`DerivedPlus.derivedComplex G ⋙ ι` (the actual right derived functor in the
unbounded derived category).

Library objects used:

- `derivedCompComparison G e A hA : D_H A ⟶ D_G (F A)`: for
  `e : F ⋙ G ≅ H` with `F` left exact and `hA` the vanishing of `R^{q+1} F A`,
  this is `(derivedResolutionIso H I).hom ≫ (derivedCompResolutionIso G e I).hom ≫
  derivedResolutionComparison G (mapAugmentation F I)` for Mathlib's chosen
  injective resolution `I` of `A`.
- `derivedResolutionFunctor G K = Q (G (K.extend))`, `derivedResolutionIso`,
  `derivedComparison G J φ = (derivedResolutionFunctor G).map φ ≫ (derivedResolutionIso G J).inv`,
  `compResolutionIso` and `derivedCompResolutionIso = Q.mapIso compResolutionIso`.
- `mapAugmentation F I : single₀ (F A) ⟶ F I` (module
  `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`).
- `DerivedPlus.derivedComplexCongr e : D_G ≅ D_H` for `e : G ≅ H`,
  `DerivedPlus.resolutionCongrNatIso`, `DerivedPlus.resolutionPostcompNatIso` and
  `DerivedPlus.derivedCompIso G P e = derivedPostcompIso G P ≪≫ derivedComplexCongr e`
  for an exact `P` and `e : G ⋙ P ≅ H` (modules
  `Langlands.Cohomology.DerivedExactPostcomposition` and
  `Langlands.Cohomology.DerivedExactComposition`).

## Section `ExtendHom`: chain-level transport to integer extensions

- `extendHom H G θ`: for additive `H : C ⥤ E`, `G : D ⥤ E`, complexes
  `K : CochainComplex C ℕ`, `L : CochainComplex D ℕ` and a cochain map
  `θ : H K ⟶ G L`, the cochain map `H (K.extend) ⟶ G (L.extend)` of integer
  complexes given by `(mapExtendIso H K).inv ≫ extendMap θ ≫ (mapExtendIso G L).hom`.
- `extendHom_comp`: `extendHom H G θ ≫ extendHom G P θ' = extendHom H P (θ ≫ θ')`.
- `map_extendMap_eq`: `G.map (extendMap u) = extendHom G G (G.map u)`.
- `natTrans_app_extend_eq`: for `α : G ⟶ G'`, the component of
  `NatTrans.mapHomologicalComplex α` at `K.extend` is `extendHom G G'` of its
  component at `K`.
- `compResolutionIso_hom_eq`: `(compResolutionIso G e K).hom` is
  `extendHom H G` of the inverse termwise composite isomorphism at `K`
  (definitional).

## Section `Augmentation`

- `mapAugmentation_natTrans`: for `α : F ⟶ F'`,
  `mapAugmentation F I ≫ (NatTrans.mapHomologicalComplex α _).app I.cocomplex =
  single₀.map (α.app A) ≫ mapAugmentation F' I`.
- `mapAugmentation_comp_map`: if `φ : F₁ I ⟶ J.cocomplex` satisfies
  `mapAugmentation F₁ I ≫ φ = J.ι` (for an injective resolution `J` of `F₁ A`),
  then `mapAugmentation (F₁ ⋙ F₂) I ≫ F₂.map φ = mapAugmentation F₂ J`.

## Section `Acyclic`

`isZero_rightDerived_comp_of_preservesHomology F₁ F₂ N n h`: if
`(F₁.rightDerived n).obj N` is zero and `F₂` preserves homology, then
`((F₁ ⋙ F₂).rightDerived n).obj N` is zero. Proof: compute both with Mathlib's
chosen injective resolution; exactness of the short complex in degree `n`
is preserved by `F₂`.

## Section `TwoStep`

Data: additive `F₁ : A ⥤ B`, `F₂ : B ⥤ C` (both preserving finite limits),
`G : C ⥤ E`, `H₁ : B ⥤ E`, `K : A ⥤ E`, and `e : F₂ ⋙ G ≅ H₁`,
`e₁ : F₁ ⋙ H₁ ≅ K`.

`derivedCompComparison_comp_eq` (with an `_assoc` form): for `N : A` with
`hN₁` (vanishing of `R^{q+1} F₁ N`) and `hN₂` (vanishing of `R^{q+1} F₂ (F₁ N)`),
any injective resolutions `I`, `J`, `L` of `N`, `F₁ N`, `F₂ (F₁ N)`, and
cochain maps `φ : F₁ I ⟶ J`, `ψ : F₂ J ⟶ L` compatible with the
augmentations,

```text
derivedCompComparison H₁ e₁ N hN₁ ≫ derivedCompComparison G e (F₁ N) hN₂ =
  (derivedResolutionIso K I).hom ≫ (derivedCompResolutionIso H₁ e₁ I).hom ≫
    (derivedCompResolutionIso G e (F₁ I)).hom ≫ derivedComparison G L (F₂ φ ≫ ψ).
```

Proof: the Library's independence of resolutions and lifts
(`derivedCompComparison_eq`, `derivedResolutionComparison_eq`), cancellation of
`derivedResolutionIso H₁ J`, and naturality `derivedCompResolutionIso_hom_naturality`.

`derivedCompComparison_comp_factorization`: let also `F₁' : A ⥤ B'`,
`F₂' : B' ⥤ C` (additive, preserving finite limits), `H₁' : B' ⥤ E`,
`K' : A ⥤ E`, `e' : F₂' ⋙ G ≅ H₁'`, `e₁' : F₁' ⋙ H₁' ≅ K'`, `κ : K ≅ K'` and
`c : F₁ ⋙ F₂ ≅ F₁' ⋙ F₂'`. Assume for `N : A` the vanishing hypotheses
`hN₁`, `hN₂`, `hN₁'`, `hN₂'` (as above for both factorizations), `hN` (vanishing
of `R^{q+1} (F₁ ⋙ F₂) N`), and for every object `Q : A`

```text
hκ : e₁.inv.app Q ≫ e.inv.app (F₁ Q) ≫ G.map (c.hom.app Q) =
       κ.hom.app Q ≫ e₁'.inv.app Q ≫ e'.inv.app (F₁' Q).
```

Then

```text
derivedCompComparison H₁ e₁ N hN₁ ≫ derivedCompComparison G e (F₁ N) hN₂ ≫
    D_G.map (c.hom.app N) =
  (derivedComplexCongr κ).hom.app N ≫ derivedCompComparison H₁' e₁' N hN₁' ≫
    derivedCompComparison G e' (F₁' N) hN₂'.
```

Proof: expand both sides with `derivedCompComparison_comp_eq`, using the same
resolution `I` of `N`; move `derivedComplexCongr κ` into the resolution model
(`derivedComplexCongr_hom_resolution`); apply the Library's
`derivedComparison_naturality` to the cochain map `c_I : F₂ F₁ I ⟶ F₂' F₁' I`,
whose source is a resolution of `F₂ F₁ N` by `hN` (`quasiIso_mapAugmentation`),
with the augmentation identities `mapAugmentation_natTrans` and
`mapAugmentation_comp_map`; the remaining identity of integer cochain maps is
reduced by the `extendHom` lemmas to an identity of natural-indexed cochain
maps, checked degreewise by `hκ`.

## Section `CongrTrans`

For additive `G H P : C ⥤ D`:

- `resolutionCongrNatIso_trans_hom_app`, `resolutionCongrNatIso_refl_hom_app`:
  composition and identity for `resolutionCongrNatIso`.
- `derivedComplexCongr_trans_hom_app`: `(derivedComplexCongr (e ≪≫ e')).hom.app X =
  (derivedComplexCongr e).hom.app X ≫ (derivedComplexCongr e').hom.app X`.
- `derivedComplexCongr_refl_hom_app`: `(derivedComplexCongr (Iso.refl G)).hom.app X = 𝟙 _`.
- `derivedComplexCongr_symm_hom_app`: `(derivedComplexCongr e.symm).hom.app X =
  (derivedComplexCongr e).inv.app X`.
- `derivedCompIso_inv_app_comp_hom_app Q e₁ e₂ X`: for an exact `Q : D ⥤ E` and
  `e₁ : G ⋙ Q ≅ H₁`, `e₂ : G ⋙ Q ≅ H₂`,
  `(derivedCompIso G Q e₁).inv.app X ≫ (derivedCompIso G Q e₂).hom.app X =
  (derivedComplexCongr (e₁.symm ≪≫ e₂)).hom.app X`.

Proofs: compare in the resolution model via `derivedComplexCongr_hom_resolution`.

## Section `ExactPostcomp`

Data: `F : C ⥤ D` additive and left exact, additive `G : D ⥤ E`, `H : C ⥤ E`,
`e : F ⋙ G ≅ H`, an exact `P : E ⥤ E'`, additive `G' : D ⥤ E'`, `H' : C ⥤ E'`,
and `eG : G ⋙ P ≅ G'`, `eH : H ⋙ P ≅ H'`, `e' : F ⋙ G' ≅ H'`, with

```text
hc : ∀ X, eH.hom.app X ≫ e'.inv.app X = P.map (e.inv.app X) ≫ eG.hom.app (F X).
```

- `compResolutionIso_hom_postcomp`: the corresponding identity of integer
  cochain maps between `P (H (K.extend))` and `G' ((F K).extend)`, checked by
  cases on the embedding `ℕ → ℤ`.
- `derivedCompComparison_postcomp A hA hc`:

  ```text
  (derivedCompIso H P eH).hom.app A ≫ derivedCompComparison G' e' A hA =
    P.mapDerivedCategory.map (derivedCompComparison G e A hA) ≫
      (derivedCompIso G P eG).hom.app (F A).
  ```

  Proof: `derivedCompIso_hom_resolution` for both exact-composite isomorphisms,
  naturality of `resolutionPostcompNatIso` and `resolutionCongrNatIso`, the
  Library's `resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app`,
  Mathlib's `Functor.mapDerivedCategoryFactors_hom_naturality`, and
  `compResolutionIso_hom_postcomp`.

## Provenance

These are internal compatibility results for the Library's own constructions,
needed by `Langlands.AlgebraicGeometry.Modules.DerivedRestriction`. They are
the standard facts that the comparison between the derived functor of a
composite and the composite of derived functors is compatible with
composition and with exact functors, stated and proved here for the
Library's specific comparison maps. They are derived internally from the
Library and Mathlib. No literature statement is formalized, and no external
mathematical assertion is used.
