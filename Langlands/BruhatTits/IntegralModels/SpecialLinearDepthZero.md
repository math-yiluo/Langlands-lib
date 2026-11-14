# Depth-zero data for `SL_n` over a local field

This module gives the hyperspecial `SL_n` regression example for the
depth-zero layer of `Langlands.BruhatTits.IntegralModels`. Earlier modules
state results for supplied `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D`. Here both are constructed for `G = SL_n`
over a nonarchimedean local field `F`, from the Library's group scheme
`SpecialLinear.groupScheme n`.

- The scheme `SL_{n,𝒪[F]}` is an integral model of `SL_{n,F}`, the standard
  model. Both of its fibres are connected reductive. It therefore gives model
  data `D` whose full and neutral models are both the standard model. `Q` is
  the identity quotient of the special fibre, from the published
  `GeneralLinearDepthZero` module.
- The module computes:
  - `G^0(𝒪) = SL_n(𝒪[F])`;
  - `G(F)^{0+}`, the kernel of reduction `SL_n(𝒪[F]) → SL_n(𝓀[F])`;
  - the index of `G(F)^{0+}` in `G^0(𝒪)`, which is `|SL_n(𝓀[F])|`. For
    `n = Fin N` this index times `q - 1` is `∏_{i < N} (q ^ N - q ^ i)`, with
    `q = Nat.card 𝓀[F]`.
- It compares these with `GL_n`. A determinant-one matrix over `F` lies in
  `G^0(𝒪)` exactly when it lies in `GL_n(𝒪[F])`. It lies in `G(F)^{0+}`
  exactly when it also lies in the level-one principal congruence subgroup.
  In rank `m + 1` the two subgroups are the preimages of the Library's
  concrete `Conductor.integralSubgroup 𝒪[F] m` and
  `Conductor.principalLevelSubgroup F m 1`.

## Provenance

The module is derived. Its statements are standard facts about `SL_n` over a
discrete valuation ring. Here they are obtained by applying published Library
results to the standard model. The task objective (Task 3557) asks for proved
examples in its "Regression examples" section. Its "Representation layer"
section asks that the Library's concrete `GL_n` results be recovered from the
general theory, with proved comparisons. The comparison here relates the
`SL_n` depth-zero subgroups to those concrete `GL_n` subgroups.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Proposition 8.4.14 (printed p. 306 / PDF p. 337), for `G` split over `K`:
  the connected model `G^0_F` of a facet `F` is reductive exactly when `F` is
  a hyperspecial vertex. In that case `G^0_F = G^1_F`, and the maximal
  reductive quotient of the special fibre is the special fibre itself. The
  identity quotient used here is this situation: the special fibre is already
  connected reductive, so the radical is trivial.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0}/P_{x,0+}` with the
  `f`-points of the reductive quotient. For `SL_n` with its reductive standard
  model this is `SL_n(𝓀[F])`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend either item. In Chapter 8 (PDF pp. 37–38) they replace the first
sentences of §8.3 and §8.4, which now assume a perfect residue field. A finite
residue field, as here, is perfect. They also amend Lemma 8.1.4,
Remark 8.3.4, 8.3.6, the proof of Theorem 8.3.13, 8.4.2, Lemma 8.4.4 and
Proposition 8.4.15. In Chapter 13 (PDF p. 49) they amend 13.5.2, 13.6.2 and
13.8.5.

KP's objects are not used in the Lean statements. The module computes the
Library's `D.neutral.integralPoints`, `Q.positivePoints` and the index for the
constructed data. The KP values above are the values these results are
compared against. The order of `GL_N(𝔽_q)` is Mathlib's
`Matrix.card_GL_field`. The relation `|SL_n| · (q - 1) = |GL_n|` is proved
here from the determinant.

## Setting

`n : Type` is a finite type with decidable equality. The model and
local-field parts assume `[Nonempty n]`, because the Library's smoothness and
reductivity results for `SL_n` take a point `p : n`. The module supplies
`Classical.arbitrary n`. The special linear group is Mathlib's
`Matrix.SpecialLinearGroup n A`.

The model part is stated for a domain `R` in universe `u` with fraction field
`K`. It uses the Library's group scheme
`SpecialLinear.groupScheme n (CommRingCat.of R)` (module `SpecialLinear`), its
points `SpecialLinear.pointsEquiv`, and its base-change isomorphism
`SpecialLinear.baseChangeModelIso` (module `SpecialLinearBaseChange`). A point
`g` over a field `K` is read as a matrix through the published
`SpecialLinear.Root.rationalMatrixEquiv K g` (module `SpecialLinearRootGroups`).

The local-field part is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
`𝒪[F]` is its valuation ring and `𝓀[F]` its residue field.

The file imports `GeneralLinearDepthZero` (for `identityQuotient` and the
`Conductor` subgroups), `Reductive.SpecialLinear` and
`SpecialLinearRootGroups`. It sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as the imported
`GeneralLinearDepthZero` does.

## Declarations

### Matrices and the standard model

These are in namespace `Langlands.GroupScheme.SpecialLinear`.

- `det_eq_one_of_map`: for an injective ring map `f : A →+* B` and a square
  matrix `M` over `A`, if `(M.map f).det = 1` then `M.det = 1`.
- `card_specialLinearGroup_mul`: over a finite field `k` and for nonempty `n`,
  `Nat.card (SL n k) * (Nat.card k - 1) = Nat.card (GL n k)`. The proof
  identifies `SL n k` with the kernel of the determinant (Mathlib's
  `Matrix.SpecialLinearGroup.toGLKerEquiv`). The determinant is surjective
  (`Matrix.GeneralLinearGroup.det_surjective`), so the kernel has index
  `Nat.card kˣ = Nat.card k - 1`.
- `matrixRingEquiv_pointsEquiv_baseChangeSectionHom`: for a ring map
  `φ : A →+* B` and a section `x` of `SL_n` over `Spec A`, consider the base
  change of `x` along `Spec φ`. Read through the base-change point
  correspondence, `pointsEquiv` and the published `Root.matrixRingEquiv`, it is
  `Matrix.SpecialLinearGroup.map φ (Root.rationalMatrixEquiv A x)`. The proof
  uses the published `baseChangePointsEquiv_baseChangeSectionHom`,
  `pointsEquiv_naturality` and `Scheme.ΓSpecIso_naturality`.
- `standardIntegralModel R K n` (definition): the `IntegralModel R K
  (groupScheme n (CommRingCat.of K))` with group `groupScheme n (CommRingCat.of
  R)` and generic identification `baseChangeModelIso n (Spec.algebraMap R K)`.
  It is affine by the published `isAffineHom_groupScheme`. It is flat and
  locally of finite type because it is smooth, by the published
  `smooth_groupScheme`.
- `standardIntegralModel_isSmooth`: the standard model is smooth.
- `standardSectionsEquiv R K n` (definition): the integral sections of the
  standard model are `Matrix.SpecialLinearGroup n R`, through
  `Root.rationalMatrixEquiv R`.
- `standardIntegralModel_integralPointMap`: the matrix of the image of an
  integral section `x` in the `K`-points is
  `Matrix.SpecialLinearGroup.map (algebraMap R K) (standardSectionsEquiv R K n
  x)`. The proof uses the published `pointsEquiv_baseChangeModelIso_hom`.
- `mem_standardIntegralModel_integralPoints`: `g` lies in the integral points
  of the standard model exactly when its matrix is
  `Matrix.SpecialLinearGroup.map (algebraMap R K) u` for some
  `u : Matrix.SpecialLinearGroup n R`.

### The local-field depth-zero data

These are in namespace `Langlands.BruhatTits.IntegralModels`.

- `isConnectedReductive_specialLinearSpecialFibre`: the special fibre of the
  standard model over `𝒪[F]` is connected reductive. This is the published
  `SpecialLinear.isConnectedReductive 𝓀[F] n p`, transported by
  `IsConnectedReductive.of_iso` along `baseChangeModelIso`.
- `specialLinearModelData F n` (definition): the
  `RelativeComponentModelData 𝒪[F] F (SpecialLinear.groupScheme n
  (CommRingCat.of F))` whose full and neutral models are both
  `SpecialLinear.standardIntegralModel 𝒪[F] F n`. It is the published
  `IntegralModel.relativeComponentData_of_reductive_localField`, applied to
  `SpecialLinear.isConnectedReductive F n p` and the previous item.
- `specialLinearModelData_neutral`: the neutral model is the standard model
  (by `rfl`).
- `specialLinearQuotientData F n` (definition): `identityQuotient` of
  `specialLinearModelData F n`.
- `specialLinearQuotientData_isReductiveQuotient`: it satisfies
  `IsReductiveQuotient`, by `identityQuotient_isReductiveQuotient`.
- `specialLinearSpecialFibrePointsEquiv F n` (definition): a group
  isomorphism `rationalPoints (specialLinearModelData F n).neutral.specialFibre
  ≃* Matrix.SpecialLinearGroup n 𝓀[F]`. It composes the published base-change
  point correspondence along `IntegralModel.residueBaseMap 𝒪[F]`, the
  published `SpecialLinear.pointsEquiv` and `Root.matrixRingEquiv` of
  `Γ(Spec 𝓀[F], ⊤) ≃+* 𝓀[F]`.
- `specialLinearSpecialFibrePointsEquiv_reduction`: for an integral section
  `x`, the matrix of its reduction is
  `Matrix.SpecialLinearGroup.map (IsLocalRing.residue 𝒪[F])
  (SpecialLinear.standardSectionsEquiv 𝒪[F] F n x)`.
- `specialLinear_index_positivePoints_subgroupOf`: the index of `G(F)^{0+}` in
  `G^0(𝒪)`, as `Subgroup.subgroupOf` of
  `(specialLinearQuotientData F n).positivePoints` in
  `(specialLinearModelData F n).neutral.integralPoints`, is
  `Nat.card (Matrix.SpecialLinearGroup n 𝓀[F])`. The proof applies the
  published `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf`
  and transfers along `specialLinearSpecialFibrePointsEquiv`.
- `specialLinear_index_positivePoints_subgroupOf_mul`: for `N` with
  `[NeZero N]` and `n = Fin N`, the same index times `Nat.card 𝓀[F] - 1` is
  `∏ i : Fin N, (Nat.card 𝓀[F] ^ N - Nat.card 𝓀[F] ^ (i : ℕ))`. It combines
  the previous item, `card_specialLinearGroup_mul` and Mathlib's
  `Matrix.card_GL_field`.
- `mem_specialLinear_positivePoints`: `g` lies in
  `(specialLinearQuotientData F n).positivePoints` exactly when there is
  `u : Matrix.SpecialLinearGroup n 𝒪[F]` with
  `Matrix.SpecialLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1` and
  `SpecialLinear.Root.rationalMatrixEquiv F g =
  Matrix.SpecialLinearGroup.map (algebraMap 𝒪[F] F) u`.
- `mem_specialLinear_integralPoints`: `g` lies in
  `(specialLinearModelData F n).neutral.integralPoints` exactly when its
  matrix is `Matrix.SpecialLinearGroup.map (algebraMap 𝒪[F] F) u` for some
  `u : Matrix.SpecialLinearGroup n 𝒪[F]`.

### Comparison with `GL_n` and the concrete `Conductor` subgroups

These are also in namespace `Langlands.BruhatTits.IntegralModels`. They use
Mathlib's `Matrix.SpecialLinearGroup.toGL`.

- `mem_specialLinear_integralPoints_iff_generalLinear`: `g` lies in `G^0(𝒪)`
  exactly when `toGL` of its matrix is
  `Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u` for some
  `u : GL n 𝒪[F]`. So `G^0(𝒪)` is `SL_n(F) ∩ GL_n(𝒪[F])`.
- `mem_specialLinear_positivePoints_iff_generalLinear`: `g` lies in
  `G(F)^{0+}` exactly when there is such a `u` that also satisfies
  `Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1`.

  Both converse directions use `det_eq_one_of_map`: an integral invertible
  matrix whose image in `F` has determinant one has determinant one over
  `𝒪[F]`.
- `specialLinear_integralPoints_eq_comap_integralSubgroup`: for `m : ℕ`,
  `(specialLinearModelData F (Fin (m + 1))).neutral.integralPoints` is the
  preimage of the published `Conductor.integralSubgroup 𝒪[F] m` under
  `Matrix.SpecialLinearGroup.toGL` composed with
  `SpecialLinear.Root.rationalMatrixEquiv F`.
- `specialLinear_positivePoints_eq_comap_principalLevelSubgroup`: in the same
  way, `(specialLinearQuotientData F (Fin (m + 1))).positivePoints` is the
  preimage of the published `Conductor.principalLevelSubgroup F m 1`. The
  proof unfolds it to the image of the published
  `Conductor.principalCongruenceSubgroup` for the ideal `𝔪 ^ 1 = 𝔪`.

## Scope

No building and no point `x` appear. Nothing here identifies the standard
model with KP's `G^0_x` for a hyperspecial vertex, or with a finite-type Néron
model. `G^0(𝒪)` is not identified with KP's `P_{x,0}`, and `G(F)^{0+}` is not
identified with `P_{x,0+}`. The equalities with KP's values hold only through
the explicit descriptions above. Only the standard model is treated. Other
vertices, non-hyperspecial parahorics and inner forms are not covered.
`n` must be nonempty. The comparison with the concrete `Conductor` subgroups
covers ranks `m + 1 ≥ 1` and only level one. The closed formula for
`|SL_n(𝓀[F])|` is given only after multiplying by `q - 1`. No division is
stated.
