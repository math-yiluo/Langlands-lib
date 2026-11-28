# Germs of differentials in the Kähler differentials of a local ring

Module `Langlands.AlgebraicGeometry.StalkKaehler`, namespace
`Langlands.AlgebraicGeometry.StalkKaehler`. It imports `Langlands.MathlibBase` and the
weil-conjectures modules `WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections`
(sections of `Ω¹_{Y/κ}` over an affine open as Kähler differentials) and
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (free generators of a sheaf of modules
on an open).

Let `g : Y ⟶ Spec κ` be a scheme over a commutative ring `κ`, `y` a point of `Y`, and let the
local ring `𝒪_{Y,y}` carry a `κ`-algebra structure that is compatible with `g`: the hypothesis

`hκ : ∀ U ∋ y, germ_y ∘ (g.specStructureMap U) = algebraMap κ 𝒪_{Y,y}`

says that on every open `U ∋ y`, the structure map `κ → Γ(Y, U)` of `g` followed by the germ at
`y` is the given algebra map. For an affine open `U ∋ y` the weil-conjectures isomorphism
`AlgebraicGeometry.Scheme.Hom.kaehlerSectionsEquiv : Ω[Γ(Y, U)⁄κ] ≃ Γ(Ω¹_{Y/κ}, U)` identifies
sections with Kähler differentials, and the module defines the germ map

`toStalk g hκ U hU hy : Γ(Ω¹_{Y/κ}, U) → Ω[𝒪_{Y,y}⁄κ]`, `a · db ↦ germ(a) · d(germ b)`,

as the inverse of `kaehlerSectionsEquiv` followed by Mathlib's
`KaehlerDifferential.map κ κ Γ(Y, U) 𝒪_{Y,y}`. On sections, this is the identification of the
stalk of `Ω¹_{Y/κ}` at `y` with `Ω_{𝒪_{Y,y}/κ}`, which holds because Kähler differentials commute
with localization; the module does not construct stalks of sheaves of modules. The form on
sections is the one used for the map `f^*Ω¹_{X/κ} → Ω¹_{Y/κ}` of a morphism of curves in
`Langlands.Correspondence.Laumon.CurveDifferentialsDifferent`.

| Declaration | Statement |
|---|---|
| `germ_comp_specStructureMap_of_top` | the hypothesis `hκ` holds on every open `U ∋ y` once it holds on `U = ⊤` |
| `toStalk` | the map `Γ(Ω¹_{Y/κ}, U) → Ω[𝒪_{Y,y}⁄κ]` for an affine open `U ∋ y` |
| `toStalk_add`, `toStalk_zero` | `toStalk` is additive |
| `toStalk_smul` | `toStalk (a • s) = germ_y(a) • toStalk s` for `a ∈ Γ(Y, U)` |
| `toStalk_sectionsD` | `toStalk (d a) = D (germ_y a)`, where `d = g.sectionsD U` is the universal derivation on sections |
| `toStalk_map` | `toStalk` commutes with restriction of sections to a smaller affine open `V ∋ y` |
| `exists_linearEquiv_of_isFreeGenerator` | if `s` is a free generator of `Ω¹_{Y/κ}` on `U` (`AlgebraicGeometry.Scheme.Modules.IsFreeGenerator s`), there is an isomorphism `e : 𝒪_{Y,y} ≃ₗ[𝒪_{Y,y}] Ω[𝒪_{Y,y}⁄κ]` with `e 1 = toStalk s` |
| `span_toStalk_eq_top` | in the same situation `toStalk s` spans `Ω[𝒪_{Y,y}⁄κ]` |

## Proofs

`germ_comp_specStructureMap_of_top`: the structure map on `U` is the structure map on `⊤`
followed by restriction (`AlgebraicGeometry.Scheme.Hom.specStructureMap_map`), and the germ on
`U` after restriction from `⊤` is the germ on `⊤` (`TopCat.Presheaf.germ_res`).

`toStalk_add`, `toStalk_zero`, `toStalk_smul`, `toStalk_sectionsD`: `kaehlerSectionsEquiv` is
`Γ(Y, U)`-linear and sends `D a` to `d a` (`kaehlerSectionsEquiv_D`); `KaehlerDifferential.map`
is linear over the germ map and sends `D a` to `D (germ a)` (`KaehlerDifferential.map_D`).

`toStalk_map`: every element of `Ω[Γ(Y, U)⁄κ]` lies in the `Γ(Y, U)`-span of the `D b`
(`KaehlerDifferential.span_range_derivation`); by induction on the span it suffices to treat
`D b`, where restriction of `d b` is `d` of the restriction of `b`
(`AlgebraicGeometry.Scheme.Hom.sectionsD_map`) and the germ of a restriction is the germ
(`TopCat.Presheaf.germ_res_apply`), and scalar multiples, by `toStalk_smul` and
`Scheme.Modules.map_smul`.

`exists_linearEquiv_of_isFreeGenerator`: for affine `U`, `𝒪_{Y,y}` is the localization of
`Γ(Y, U)` at the prime of `y` (`IsAffineOpen.isLocalization_stalk`), hence a formally étale
`Γ(Y, U)`-algebra (`Algebra.FormallyEtale.of_isLocalization`). The free generator `s`
corresponds to `σ = kaehlerSectionsEquiv⁻¹ s` with `r ↦ r • σ` bijective
`Γ(Y, U) → Ω[Γ(Y, U)⁄κ]`. The isomorphism `e` is the composite
`𝒪_{Y,y} ≅ 𝒪_{Y,y} ⊗ Γ(Y, U) ≅ 𝒪_{Y,y} ⊗ Ω[Γ(Y, U)⁄κ] ≅ Ω[𝒪_{Y,y}⁄κ]`, the last map being
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, which is `mapBaseChange`; it sends `1`
to the image of `σ`, which is `toStalk s` by definition.

`span_toStalk_eq_top`: every `m` is `e (e⁻¹ m) = (e⁻¹ m) • e 1`.
