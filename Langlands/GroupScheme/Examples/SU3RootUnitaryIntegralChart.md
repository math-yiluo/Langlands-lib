# Integral charts of the quadratic unitary parameter group

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralChart`, namespace
`Langlands.GroupScheme.SU3Root`.

`L / K` is a separable quadratic field extension with conjugation `σ = conjugation K L`, and
`unitaryParameterGroup K L` is the published affine group scheme `U_{L/K}` over `Spec K` of
`Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates`. Its points over a test scheme `T`
are the pairs `(u, v)` in `Γ(T) ⊗[K] L` with `v + bar(v) = u bar(u)` and the law of KP (2.7.2).
A *chart* `D : CoordinateData K L ι` is a `K`-basis `e` of `L`, an element `λ` with
`λ + σ λ = 1`, a nonzero `f` with `f + σ f = 0`, and the coefficients `cᵢⱼ ∈ K` with
`cᵢⱼ f = correction λ eᵢ eⱼ = σ(λ) eᵢ σ(eⱼ) − λ σ(eᵢ) eⱼ`. Through
`toParameters D`, `U_{L/K}` is the bilinear coordinate group with coefficients `cᵢⱼ`:
`(a, b) ↦ (u, v) = (∑ᵢ aᵢ eᵢ, b f + λ u σ(u))`, the inverse of the coordinate change (C.4.1),
with the group law (C.4.2).

This module carries out the construction of Kaletha–Prasad Appendix C.4 (C.4.1)–(C.4.2) for an
arbitrary chart whose coefficients are integral. The lattice charts that give the models
`X_{r,s}` themselves are in `Langlands.GroupScheme.Examples.SU3RootUnitaryIntegralModel`.

## Coefficient changes

- `coordinatesCongr e h`: a ring isomorphism `e : S ≃+* T` sending the coefficients `cᵢⱼ` to
  `dᵢⱼ` gives an isomorphism of bilinear coordinate groups `Coordinates c ≃* Coordinates d`,
  entrywise `e` (`vec_coordinatesCongr`, `scalar_coordinatesCongr`).

## Changes of chart

Here `k` is any field and `L / k` a separable quadratic extension.

- `correction_sum_sum`: the correction is `k`-bilinear for finite linear combinations.
- `CoordinateData.IsChartChange D D' M t` (for `M : ι → κ → k`, `t : k`) says that the two
  charts have the same `λ`, that `eᵢ = ∑ₗ Mᵢₗ e'ₗ`, and that `f = t f'`.
- `IsChartChange.isCompatible`: then `∑ₚ ∑_q Mᵢₚ Mⱼ_q c'ₚ_q = t cᵢⱼ`, which is the condition
  `IsCompatible` of `Langlands.GroupScheme.BilinearCoordinateGroup`. Proof: multiply by `f'`,
  expand `correction λ eᵢ eⱼ` bilinearly in the `e'ₗ`, and use `c'ₚ_q f' = correction λ e'ₚ e'_q`
  and `f = t f'`.
- `IsChartChange.tensorVec_matrixVec`: `∑ₗ (∑ᵢ aᵢ Mᵢₗ) ⊗ e'ₗ = ∑ᵢ aᵢ ⊗ eᵢ`.
- **`IsChartChange.toParameters_linearMap`**: over every `k`-algebra `S`, the identifications
  of the two charts differ by the coordinate change `(a, b) ↦ (M a, t b)` (`Coordinates.linearMap`),
  that is, `toParameters D' S (M a, t b) = toParameters D S (a, b)`. The first coordinates agree
  by `tensorVec_matrixVec`; for the second, `t b ⊗ f' = b ⊗ t f' = b ⊗ f` and both charts use the
  same `λ`.

## Integral charts and their models

From now on `O` is a domain with fraction field `K` (`IsFractionRing O K`), and `O`, `K`, `L`
live in one universe.

- `IntegralChart O K L ι` is a chart `data : CoordinateData K L ι` together with coefficients
  `coeff : ι → ι → O` whose images in `K` are the chart coefficients (`algebraMap_coeff`).
- `IntegralChart.group C` is the bilinear coordinate group scheme over `Spec O` with the
  coefficients `C.coeff` (`BilinearCoordinate.groupScheme`), that is, `Spec O[aᵢ, b]` with the
  law `(a, b)(a', b') = (a + a', b + b' + ∑ᵢⱼ cᵢⱼ aᵢ a'ⱼ)` of (C.4.2) in coordinates.
- `restrictedSections T`: for a test scheme `T` over `Spec K`, the global sections of `T` as an
  `O`-algebra through `Spec K → Spec O`; it is also a `K`-algebra, compatibly
  (`restrictedSectionsScalarTower`, `algebraMap_restrictedSections`).
- `genericPointsEquiv C T`: the points of the generic fibre of `C.group` over a test scheme `T`
  over `Spec K` are `tensorParameters K L Γ(T)`. It composes the published
  `GroupScheme.baseChangePointsEquiv` (points of the base change are points over `Spec O`), the
  published `BilinearCoordinate.pointsEquiv` (points are bilinear coordinates in the sections),
  `sectionsCoordinatesEquiv` (the coefficients through `O` and through `K` agree), and
  `toParameters C.data`. It is natural in `T` (`genericPointsEquiv_naturality`).
- **`IntegralChart.model C : IntegralModel O K (unitaryParameterGroup K L)`** is the published
  `IntegralModel` structure with group `C.group` (affine, flat and locally of finite type by the
  helper module) and generic identification given by the published `isoOfPointModels`: both the
  generic fibre and `U_{L/K}` have the natural point model `T ↦ tensorParameters K L Γ(T)` on
  **all** test schemes over `Spec K`, via `genericPointsEquiv` and the published
  `unitaryPointsEquiv`. `unitaryPointsEquiv_genericIso` records that on points the generic
  identification is `genericPointsEquiv`.
- `model_isSmooth`: the model is smooth (`IntegralModel.IsSmooth`), and
  `model_geometricallyConnected`: its structure morphism has geometrically connected fibres; both
  come from the helper module.

## Integral points

- `integralCoordinatesEquiv C`: the sections of the model over `Spec O` are the bilinear
  coordinates with entries in `O`, as groups (`Coordinates C.coeff`), via
  `BilinearCoordinate.pointsEquiv` at the identity test scheme and the published
  `identitySectionsEquiv`. `vec_integralCoordinatesEquiv` and `scalar_integralCoordinatesEquiv`
  unfold it.
- `fieldPoint D a b ∈ rationalParameters K L` is the field point with chart coordinates
  `(a, b) ∈ K^ι × K`; `first_fieldPoint`: `u = ∑ᵢ aᵢ eᵢ`; `second_fieldPoint`:
  `v = b f + λ u σ(u)`.
- **`unitaryRationalPointsEquiv_integralPointMap`**: the image in
  `rationalParameters K L` (through the published `unitaryRationalPointsEquiv`) of an integral
  section with `O`-coordinates `(a, b)` is `fieldPoint C.data a b`.
- **`mem_integralPoints_iff`**: a rational point `g` of `U_{L/K}` lies in the published subgroup
  `C.model.integralPoints` if and only if it is the field point of chart coordinates
  `a : ι → O`, `b : O`. Equivalently the integral points are `{(u, v) : u = ∑ aᵢ eᵢ,
  v − λ u σ(u) = b f, aᵢ, b ∈ O}`, the image of `Y × Z` under the inverse of (C.4.1) when `e`
  is an `O`-basis of `Y` and `f` an `O`-generator of `Z`.

## Model homomorphisms from integral changes of chart

Let `C : IntegralChart O K L ι` and `C' : IntegralChart O K L κ`, and let `M : ι → κ → O`,
`t : O` be such that `C.data.IsChartChange C'.data M t` (over `K`).

- `isCompatible_of_isChartChange`: then `IsCompatible C.coeff C'.coeff M t` over `O`, since
  `O → K` is injective.
- **`chartHom C C' M t h : C.model.Hom C'.model (𝟙 _)`** is a published `IntegralModel.Hom`
  over the identity of `U_{L/K}`. Its group-scheme map is the published
  `BilinearCoordinate.linearHom O M t`, given on coordinates by `(a, b) ↦ (M a, t b)`. The
  generic compatibility square is checked on points over every test scheme (`hom_ext_points`),
  where it reduces to `IsChartChange.toParameters_linearMap`.
- `integralCoordinatesEquiv_chartHom`: on integral sections `chartHom` acts by
  `(a, b) ↦ (M a, t b)` in the coordinates of `integralCoordinatesEquiv`.

## Relation to the literature

KP (C.4.1) replaces `(u, v)` by `(u, x)` with `x = v − u σ(u) λ`, and (C.4.2) gives the group
law `(u, x)(u', x') = (u + u', x + x' + σ(λ) u σ(u') − λ σ(u) u')` on `L × L^0`. KP then take
the scheme `Y × Z` associated to `O`-lattices `Y ⊂ L` and `Z ⊂ L^0`. Here `Y` is presented by
the `O`-basis `e` and `Z` by the generator `f`, and the law (C.4.2) becomes the bilinear law
with coefficients `cᵢⱼ`. The structures `IntegralChart` and `IsChartChange` and the
point-model construction of the generic identification are internal devices for this
presentation; they are not in KP.
