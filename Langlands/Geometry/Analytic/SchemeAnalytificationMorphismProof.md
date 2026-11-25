# Proof: analytifications of morphisms of schemes exist, are unique and are functorial

Lean module: `Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof`.

Main theorem:
`Langlands.Analytic.SchemeAnalytification.schemeAnalytificationMorphism`, of type
`SchemeAnalytificationMorphismStatement.{u}`. It proves the unchanged published
statement in every universe `u`. The statement and its sources are described in
the paired Markdown of `Langlands.Geometry.Analytic.SchemeAnalytificationMorphismStatement`.

The proof makes no assumption beyond the statement's. `K` is a complete,
ultrametric, nontrivially normed field. `X`, `Y` and `Z` are schemes locally of
finite type over `Spec K`, and `g`, `g'` are morphisms over `Spec K`. No
separatedness or quasi-compactness is used. In particular the proof does not
depend on the published `SchemeAnalytificationGluingStatement` or
`AnalytificationCenterStatement` (proved separately in
`SchemeAnalytificationGluingProof` and `AnalytificationCenterProof`). The facts it needs from them are proved by
the imported helper modules listed below.

## Assembly

The first part of the statement is the conjunction of
`MorphismExistence.existsUnique_isAnalytificationMap` (item 1) and
`MorphismCompatibility.compatibility` (items 2 and 3, imported from
`SchemeAnalytificationMorphismCompatibilityProof`). The second part (item 4) is
`MorphismExistence.isAnalytificationMap_comp`.

## Affine lemmas (namespace `AffineAnalytification.MorphismComparison`)

- `baseMap_baseMap`: if `f₂ ∘ f₁ = f₃` pointwise for `K`-algebra maps, then the
  induced maps of affine analytifications compose accordingly.
  `baseMap_eq_self`: an algebra map fixing every element induces the identity.
  Both are proved by injectivity of the point-seminorm map
  (`SeminormComparison.pointSeminorm_injective`) and the published
  `pointSeminorm_baseMap`.
- `isOpenEmbedding_baseMap_of_localization`: a `K`-algebra map which, viewed as
  an algebra structure, is a localization away from one element induces an open
  embedding. It installs that algebra structure and the scalar tower, then
  applies `ImmersionComparison.isOpenEmbedding_baseMap_away`.

## Restriction and induced maps (namespace `MorphismExistence`)

- Algebraic identities: `restriction_restriction`, `restriction_self`,
  `restriction_openCoordinateMap` and `openCoordinateMap_restriction`. They
  follow from Mathlib's `Scheme.homOfLE_homOfLE`, `Scheme.homOfLE_rfl`,
  `Scheme.Hom.map_resLE` and `Scheme.Hom.resLE_map`, applied through `appTop`.
- These identities and `baseMap_baseMap` give the analytic identities
  `localMap_localMap` (restriction maps compose), `localMap_self`,
  `morphismLocalMap_localMap` (shrinking the source affine open),
  `localMap_morphismLocalMap` (enlarging the target affine open) and
  `morphismLocalMap_comp`. The last one uses the published
  `openCoordinateMap_comp`.
- `isOpenEmbedding_localMap_basicOpen`: restriction from an affine open `U` to
  its principal affine open `X.affineBasicOpen a` is an open embedding. The
  coordinate restriction is a localization away from the generator by
  `CenterRange.isLocalization_restriction_basicOpen`.
- `range_localMap`: for affine opens `V ⊆ U`, the range of the restriction map
  `Vᵃⁿ → Uᵃⁿ` is the inverse image of `V` under the local center. This is
  `CenterRange.range_localMap` with the principal-open range data
  `OpenGluing.basicOpenRangeData`.
- `localMap_injective`: every restriction map `Vᵃⁿ → Uᵃⁿ` is injective. If two
  points of `Vᵃⁿ` have the same image, their centers agree by
  `localCenter_localMap`. Choose a principal open `D` of `U` inside `V`
  containing that center. By `range_localMap` for `D ⊆ V`, both points come from
  `Dᵃⁿ`. By `localMap_localMap` their preimages have the same image under the
  composite restriction `Dᵃⁿ → Uᵃⁿ`, which is injective by
  `isOpenEmbedding_localMap_basicOpen`.

## Existence

For a point `y` of `Uᵃⁿ`, a `LocalDatum` consists of affine opens `D ⊆ U` of `X`
and `V` of `Y` with `D ⊆ g⁻¹(V)`, and a point `w` of `Dᵃⁿ` restricting to `y`.
Its value is `ι_Y V (morphismLocalMap g D V w)` in the glued analytification of
`Y`.

- `exists_basicOpen_datum` (hence `nonempty_localDatum`): every point has a
  datum with `D` a principal open of `U`. Choose an affine open `V` of `Y`
  containing the image under `g` of the center of `y`. Choose a principal open
  `D` of `U` containing the center and contained in `g⁻¹(V)`. The point lifts to
  `Dᵃⁿ` by `OpenGluing.range_localMap_basicOpen`.
- `LocalDatum.value_eq`: the value does not depend on the datum. Given two data,
  the center of `y` lies in both `D`s, and its image lies in both `V`s. Choose an
  affine open `V₃` of `Y` inside both `V`s containing the image. Choose a
  principal open `D₃` of `U` inside both `D`s and `g⁻¹(V₃)` containing the
  center. Lift `y` to `w₃` in `D₃ᵃⁿ`. By `localMap_injective`, `w₃` restricts to
  the `w` of each datum. Then `morphismLocalMap_localMap`, the published
  `ι_localMap` and `localMap_morphismLocalMap` rewrite both values to
  `ι_Y V₃ (morphismLocalMap g D₃ V₃ w₃)`.
- `localFun g U` sends `y` to the value of a chosen datum, and `localFun_eq`
  shows that it equals the value of every datum.
- `continuous_localFun`: continuity is local. Near `y`, take a principal datum
  `(D, V, w)`. On the range of the open embedding `Dᵃⁿ → Uᵃⁿ`, `localFun g U`
  composed with it equals `ι_Y V ∘ morphismLocalMap g D V`, which is continuous.
  `IsOpenEmbedding.continuousAt_iff` transfers continuity at `w` to continuity
  at `y`.
- `localFun_localMap`: the local functions are compatible with restriction,
  because a datum for a point of `U'ᵃⁿ` is also a datum for its image in `Uᵃⁿ`.
- `analytification g` is the map glued from the local functions by the
  published `desc`. `isAnalytificationMap_analytification` holds because, for
  `U ⊆ g⁻¹(V)`, the tuple `(U, V, y)` is itself a datum for `y`.

## Uniqueness

`apply_ι_eq_value`: every map `F` satisfying `IsAnalytificationMap` takes at
`ι_X U y` the value of every datum `(D, V, w)` of `y`. Indeed
`ι_X U y = ι_X D w` by `ι_localMap`, and the defining equation of `F` on
`D ⊆ g⁻¹(V)` gives the value. So any such `F` agrees with `analytification g`
on every chart. The published `desc_unique` then gives `F = analytification g`.
This is `existsUnique_isAnalytificationMap`.

## Composition

`isAnalytificationMap_comp`: let `F` and `F'` be analytifications of `g` and
`g'`, and let `U ⊆ (g ≫ g')⁻¹(W)` with `y` in `Uᵃⁿ`. Choose an affine open `V` of
`Y` inside `g'⁻¹(W)` containing the image of the center of `y`. Choose a
principal open `D` of `U` inside `g⁻¹(V)` containing the center, and lift `y` to
`w` in `Dᵃⁿ` by `OpenGluing.range_localMap_basicOpen`. Then
`F' (F (ι_X D w)) = ι_Z W (m_{g'} (m_g w))` by the defining equations of `F` on
`D ⊆ g⁻¹(V)` and of `F'` on `V ⊆ g'⁻¹(W)`. Finally `morphismLocalMap_comp` and
`morphismLocalMap_localMap` identify this with the defining value for
`g ≫ g'` on `U ⊆ (g ≫ g')⁻¹(W)`.

## Imported helper modules

The proof uses the following helper modules. Existing published helpers are
reused. Each of these modules has paired Markdown.

- `AffineAnalytificationSeminormProof`: the affine seminorm comparison. It
  supplies `SeminormComparison.pointSeminorm_injective`.
- `AffineAnalytificationImmersionProof`: the affine immersion proof. It
  supplies `ImmersionComparison.isOpenEmbedding_baseMap_away`.
- `SchemeAnalytificationBasicOpen`, `SchemeAnalytificationCenterRangeProof`
  and `SchemeAnalytificationBasicOpenRangeProof`: the coordinate localization
  bridge, the center-range reductions and the principal-open range adapter.
- `AnalytificationCenterComparison`: the published rational-center helpers,
  reused directly.
- `SchemeAnalytificationMorphismCompatibility` and
  `SchemeAnalytificationMorphismCompatibilityProof`: the center and
  rational-point compatibility.

The existence, uniqueness and composition arguments and the final assembly in
this module are an internal derivation of the clauses of the published target. The target's mathematical sources are Berkovich 1990,
Theorem 3.4.1 and steps (2)–(3) of its proof, and Conrad–Temkin 2009,
Theorem 2.2.3, as cited in the target's paired Markdown. This Lean proof does not
follow their route through a universal property. It works with the explicit
predicate `IsAnalytificationMap` and patches local maps on principal affine
opens.
