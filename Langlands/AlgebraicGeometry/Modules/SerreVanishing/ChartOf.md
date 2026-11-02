# Module charts of the iterated twists

Internal helper module for the proof of `TwistKillingStatement` (module
`SerreVanishing.Iterate`). It turns the identifications `twistChartIso` of module
`SerreVanishing.Chart` into module charts `ModChart` (module `SerreVanishing.Glue`) for
the system `(twistIter N m).obj Z` with transition maps `(stepNat N s m).app Z`. The charts
are natural in `Z`.

## Naturality

For `T : X.Opens`, `L : X.Modules` and a trivialization `e : L.restrict T.ι ≅ 𝒪_T`:

- `stripIso_naturality`: for `g : A ⟶ B`,
  `T.ι^*((twistIter L m).map g) ≫ (stripIso T L e B m).hom =
  (stripIso T L e A m).hom ≫ T.ι^* g`.
- `twistChartIso_naturality`: the same for `twistChartIso` and the restriction functor.

## Transport of sections

For an open `T` and an isomorphism `Ψ : M.restrict T.ι ≅ Z.restrict T.ι`, `modE Ψ W hW`
sends a section of `M` over an open `W ≤ T` to a section of `Z` over `W`. It restricts the
section to the image of `T.ι ⁻¹ᵁ W` and reads it as a section of `M.restrict T.ι` over
`T.ι ⁻¹ᵁ W`. Then it applies `Ψ` and reads the result back as a section of `Z` over `W`.
The Library helpers `ofImage`, `toImage` and `le_image_preimage` of
`LineBundleSectionClearingProof` do the two readings. The lemmas `toImage_map`,
`toImage_app`, `toImage_smul` record how `toImage` interacts with restriction, morphisms
and scalars; all three hold by `rfl`.

- `modE_symm_modE`: `modE Ψ.symm W hW (modE Ψ W hW d) = d`. Hence `modE_injective` and
  `modE_surjective`.
- `modE_res`: `modE` commutes with restriction.
- `modE_smul`: `modE` is linear over `Γ(X, W)`.
- `modE_naturality`: suppose `f : M ⟶ M'` and `g : Z ⟶ Z'` satisfy
  `f|_T ≫ Ψ'.hom = Ψ.hom ≫ g|_T`. Then `modE Ψ' (f d) = g (modE Ψ d)`.
- `modE_mul`: suppose `Ψ' : M'.restrict T.ι ≅ Z.restrict T.ι`, `f : M ⟶ M'` and an
  endomorphism `φ` of `𝒪_T` satisfy `f|_T ≫ Ψ'.hom = Ψ.hom ≫ (φ(1) • 𝟙)`. Then
  `modE Ψ' W hW (f d) = (chartCoeff φ)|_W • modE Ψ W hW d`, where `chartCoeff φ ∈ Γ(X, T)`
  is the Library's transport of `φ(1)` to `T ⊆ X`.

## The charts

For `N : X.Modules`, `s : GlobalSections N`, `T` and a trivialization `e` of `N` over `T`,
`twistModChart N s T e Z` is the module chart

`ModChart (fun m => (twistIter N m).obj Z) (fun m => (stepNat N s m).app Z) Z T
  (chartCoeff (chartMulOf T N e (sectionHom N s)))`

with coordinates `E m W hW := modE (twistChartIso T N e Z m) W hW`. The fields are the
lemmas above. `mul` is `modE_mul` applied to `twistChartIso_succ`.
`twistModChart_naturality` says that for `g : A ⟶ B` the coordinates satisfy
`E_B ((twistIter N m).map g d) = g (E_A d)`. It is `modE_naturality` applied to
`twistChartIso_naturality`.

## Proofs

Both naturality lemmas are proved by induction on `m`. The step uses the naturality of
the pullback tensor comparison (`pullbackTensorComparisonApp_naturality`), functoriality
of `tensorMap` and the naturality of the right unitor (`tensorRightUnitor_naturality`).
The `modE` lemmas unfold the definition and use the Library's section-level lemmas
`modules_map_map`, `modules_map_id`, `ofImage_toImage`, `ofImage_map`, `ofImage_smul`,
`ofImage_app`, `hom_app_map` and `appIso_inv_res`. For `modE_mul`, multiplication by `φ(1)`
on `T` is read on `T.ι ⁻¹ᵁ W` and transported to `W` by `appIso_inv_res`.

## Provenance

Derived for this proof. The construction generalizes the Library's line-bundle charts
`chartE` (`LineBundleSectionClearingProof`) from the powers of `N` to the twists of an
arbitrary module. Its mathematical content is the local description of multiplication by
`s` on a trivializing open, as in the proof of Stacks Project, Lemma 28.18.2 (tag
[01PW](https://stacks.math.columbia.edu/tag/01PW)).
