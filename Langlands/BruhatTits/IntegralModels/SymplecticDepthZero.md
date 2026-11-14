# Depth-zero data for split `Sp_{2l}` over a local field

This module gives the hyperspecial split symplectic regression example for
the depth-zero layer of `Langlands.BruhatTits.IntegralModels`. Earlier
modules state results for supplied `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D`. Here both are constructed for
`G = Sp_{2l}` over a nonarchimedean local field `F`, from the Library's
coordinate group scheme `SymplecticMatrix.groupScheme l`.

- The coordinate scheme over `𝒪[F]` is an integral model of `Sp_{2l,F}`, the
  standard model. Both of its fibres are connected reductive. It therefore
  gives model data `D` whose full and neutral models are both the standard
  model. `Q` is the identity quotient of the special fibre, from the published
  `GeneralLinearDepthZero` module.
- The module computes:
  - `G^0(𝒪) = Sp_{2l}(𝒪[F])`;
  - `G(F)^{0+}`, the kernel of reduction `Sp_{2l}(𝒪[F]) → Sp_{2l}(𝓀[F])`;
  - the index of `G(F)^{0+}` in `G^0(𝒪)`, which is `|Sp_{2l}(𝓀[F])|`.
- It compares these with `GL_{l ⊕ l}`. A symplectic matrix over `F` lies in
  `G^0(𝒪)` exactly when it lies in `GL_{l ⊕ l}(𝒪[F])`, that is, when all its
  entries are integral. It lies in `G(F)^{0+}` exactly when it also lies in the
  level-one principal congruence subgroup of `GL_{l ⊕ l}(𝒪[F])`.

## Provenance

The module is derived. Its statements are standard facts about the split
symplectic group over a discrete valuation ring. Here they are obtained by
applying published Library results to the coordinate model. The task
objective (Task 3557) asks for proved examples in its "Regression examples"
section. This unit is a semisimple example, beside the `GL_N` example of
`GeneralLinearDepthZero`.

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
  `f`-points of the reductive quotient. For split `Sp_{2l}` with its reductive
  coordinate model this is `Sp_{2l}(𝓀[F])`.

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
compared against. The index is stated as `Nat.card (Matrix.symplecticGroup l
𝓀[F])`. The closed formula `q ^ (l ^ 2) ∏_{i = 1}^{l} (q ^ (2 i) - 1)` is not
proved: neither Mathlib nor the Library has it.

## Setting

`l : Type` is a finite type with decidable equality. Matrices are indexed by
`l ⊕ l`, and the symplectic group is Mathlib's `Matrix.symplecticGroup l A`
for the standard form `Matrix.J l A`. No nonemptiness is assumed; for empty
`l` the group is trivial.

The model part is stated for a domain `R` in universe `u` with fraction field
`K`. It uses the Library's group scheme
`SymplecticMatrix.groupScheme l (CommRingCat.of R)` (module
`SymplecticMatrix.Basic`), its points `SymplecticMatrix.pointsEquiv`, and its
base-change isomorphism `SymplecticMatrix.baseChangeModelIso`. A point `g` over
a field `K` is read as a symplectic matrix through
`SymplecticMatrix.rationalPointsEquiv l (CommRingCat.of K) g`, defined below.

The local-field part is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
`𝒪[F]` is its valuation ring and `𝓀[F]` its residue field.

The file imports `GeneralLinearDepthZero` (for `identityQuotient`) and
`SymplecticMatrix.Reductive`. It sets `backward.isDefEq.respectTransparency`
and `backward.isDefEq.respectTransparency.types` to `false`, as the imported
`GeneralLinearDepthZero` does.

## Declarations

### Symplectic matrices and the standard model

These are in namespace `Langlands.GroupScheme.SymplecticMatrix`.

- `mapEquiv φ` (definition): for a ring isomorphism `φ : A ≃+* B`, the group
  isomorphism `Matrix.symplecticGroup l A ≃* Matrix.symplecticGroup l B` that
  applies `φ` to every entry. Its maps are the published `map l φ` and
  `map l φ.symm`.
- `mapEquiv_apply`: the `(i, j)` entry of `mapEquiv φ g` is `φ` of the
  `(i, j)` entry of `g`.
- `mem_symplecticGroup_of_map_mem`: for an injective ring map `f : A →+* B`
  and a matrix `M` over `A`, if `M.map f` is symplectic then `M` is
  symplectic. The proof applies `f` to `M * J * Mᵀ = J`, using Mathlib's
  `Matrix.map_J`.
- `rationalPointsEquiv l R` (definition): the points of `groupScheme l R`
  over `Spec R` itself are `Matrix.symplecticGroup l R`. It is the published
  `pointsEquiv` followed by `mapEquiv` of the published
  `GeneralLinear.globalSectionsEquiv R : Γ(Spec R, ⊤) ≃+* R`.
- `mapEquiv_pointsEquiv_baseChangeSectionHom`: for a ring map `φ : A →+* B`
  and a section `x` of `Sp_{2l}` over `Spec A`, consider the base change of
  `x` along `Spec φ`. Read through the base-change point correspondence,
  `pointsEquiv` and `mapEquiv`, it is `map l φ (rationalPointsEquiv l _ x)`.
  The proof uses the published `baseChangePointsEquiv_baseChangeSectionHom`,
  `pointsEquiv_naturality` and `Scheme.ΓSpecIso_naturality`.
- `standardIntegralModel R K l` (definition): the `IntegralModel R K
  (groupScheme l (CommRingCat.of K))` with group `groupScheme l (CommRingCat.of
  R)` and generic identification `baseChangeModelIso l (Spec.algebraMap R K)`.
  It is affine by the published `isAffineHom_groupScheme`. It is flat and
  locally of finite type because it is smooth, by the published
  `smooth_groupScheme`.
- `standardIntegralModel_isSmooth`: the standard model is smooth.
- `standardSectionsEquiv R K l` (definition): the integral sections of the
  standard model are `Matrix.symplecticGroup l R`, through
  `rationalPointsEquiv l (CommRingCat.of R)`.
- `standardIntegralModel_integralPointMap`: the matrix of the image of an
  integral section `x` in the `K`-points is
  `map l (algebraMap R K) (standardSectionsEquiv R K l x)`. The proof uses the
  published `pointsEquiv_baseChangeModelIso_hom`.
- `mem_standardIntegralModel_integralPoints`: `g` lies in the integral points
  of the standard model exactly when its matrix is
  `map l (algebraMap R K) u` for some `u : Matrix.symplecticGroup l R`.
- `mem_standardIntegralModel_integralPoints_iff_entries`: equivalently, every
  entry of the matrix of `g` lies in the image of `R` in `K`. The converse
  direction uses `mem_symplecticGroup_of_map_mem` and the injectivity of
  `R → K`.

### The local-field depth-zero data

These are in namespace `Langlands.BruhatTits.IntegralModels`.

- `isConnectedReductive_symplecticSpecialFibre`: the special fibre of the
  standard model over `𝒪[F]` is connected reductive. This is the published
  `SymplecticMatrix.isConnectedReductive l 𝓀[F]`, transported by
  `IsConnectedReductive.of_iso` along `baseChangeModelIso`.
- `symplecticModelData F l` (definition): the
  `RelativeComponentModelData 𝒪[F] F (SymplecticMatrix.groupScheme l
  (CommRingCat.of F))` whose full and neutral models are both
  `SymplecticMatrix.standardIntegralModel 𝒪[F] F l`. It is the published
  `IntegralModel.relativeComponentData_of_reductive_localField`, applied to
  `SymplecticMatrix.isConnectedReductive l F` and the previous item.
- `symplecticModelData_neutral`: the neutral model is the standard model (by
  `rfl`).
- `symplecticQuotientData F l` (definition): `identityQuotient` of
  `symplecticModelData F l`.
- `symplecticQuotientData_isReductiveQuotient`: it satisfies
  `IsReductiveQuotient`, by `identityQuotient_isReductiveQuotient`.
- `symplecticSpecialFibrePointsEquiv F l` (definition): a group isomorphism
  `rationalPoints (symplecticModelData F l).neutral.specialFibre ≃*
  Matrix.symplecticGroup l 𝓀[F]`. It composes the published base-change point
  correspondence along `IntegralModel.residueBaseMap 𝒪[F]`, the published
  `SymplecticMatrix.pointsEquiv` and `mapEquiv` of
  `Γ(Spec 𝓀[F], ⊤) ≃+* 𝓀[F]`.
- `symplecticSpecialFibrePointsEquiv_reduction`: for an integral section `x`,
  the matrix of its reduction is
  `SymplecticMatrix.map l (IsLocalRing.residue 𝒪[F])
  (SymplecticMatrix.standardSectionsEquiv 𝒪[F] F l x)`.
- `symplectic_index_positivePoints_subgroupOf`: the index of `G(F)^{0+}` in
  `G^0(𝒪)`, as `Subgroup.subgroupOf` of
  `(symplecticQuotientData F l).positivePoints` in
  `(symplecticModelData F l).neutral.integralPoints`, is
  `Nat.card (Matrix.symplecticGroup l 𝓀[F])`. The proof applies the published
  `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf` and
  transfers along `symplecticSpecialFibrePointsEquiv`.
- `mem_symplectic_positivePoints`: `g` lies in
  `(symplecticQuotientData F l).positivePoints` exactly when there is
  `u : Matrix.symplecticGroup l 𝒪[F]` with
  `SymplecticMatrix.map l (IsLocalRing.residue 𝒪[F]) u = 1` and
  `SymplecticMatrix.rationalPointsEquiv l _ g =
  SymplecticMatrix.map l (algebraMap 𝒪[F] F) u`.
- `mem_symplectic_integralPoints`: `g` lies in
  `(symplecticModelData F l).neutral.integralPoints` exactly when its matrix
  is `SymplecticMatrix.map l (algebraMap 𝒪[F] F) u` for some
  `u : Matrix.symplecticGroup l 𝒪[F]`.

### Comparison with `GL_{l ⊕ l}`

These are also in namespace `Langlands.BruhatTits.IntegralModels`. They use
the published `SymplecticMatrix.toGL : Matrix.symplecticGroup l A →*
GL (l ⊕ l) A`.

- `mem_symplectic_integralPoints_iff_generalLinear`: `g` lies in `G^0(𝒪)`
  exactly when `toGL` of its matrix is
  `Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u` for some
  `u : GL (l ⊕ l) 𝒪[F]`. So `G^0(𝒪)` is `Sp_{2l}(F) ∩ GL_{l ⊕ l}(𝒪[F])`.
- `mem_symplectic_positivePoints_iff_generalLinear`: `g` lies in `G(F)^{0+}`
  exactly when there is such a `u` that also satisfies
  `Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1`. So
  `G(F)^{0+}` is the intersection of `Sp_{2l}(F)` with the kernel of reduction
  on `GL_{l ⊕ l}(𝒪[F])`.

Both converse directions use `mem_symplecticGroup_of_map_mem`: an integral
invertible matrix whose image in `F` is symplectic is symplectic over
`𝒪[F]`.

## Scope

No building and no point `x` appear. Nothing here identifies the standard
model with KP's `G^0_x` for a hyperspecial vertex, or with a finite-type Néron
model. `G^0(𝒪)` is not identified with KP's `P_{x,0}`, and `G(F)^{0+}` is not
identified with `P_{x,0+}`. The equalities with KP's values hold only through
the explicit descriptions above. Only the coordinate model of the split form
is treated. Other vertices, non-hyperspecial parahorics and non-split forms
are not covered. The `GL` comparison is with the matrix groups indexed by
`l ⊕ l`. It is not stated for the Library's `Conductor` subgroups, which are
indexed by `Fin (n + 1)`. The order of `Sp_{2l}(𝓀[F])` is not computed.
