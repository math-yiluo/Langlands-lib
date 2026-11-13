# Depth-zero data for `GL_N` over a local field

This module gives the hyperspecial `GL_N` regression example for the
depth-zero layer of `Langlands.BruhatTits.IntegralModels`. It also gives the
general construction behind it. Earlier modules state results for supplied
`D : RelativeComponentModelData R K G` and `Q : SpecialFibreQuotientData D`.

- For any `D` whose neutral special fibre is connected reductive, the module
  constructs `Q` (the identity quotient). It proves `IsReductiveQuotient` and
  identifies `Q.positivePoints` with the congruence subgroup of the neutral
  model.
- For `G = GL_N` over a nonarchimedean local field `F`, it constructs `D`
  from the Library's standard model `GL_{N,𝒪[F]}` and computes:
  - `G^0(𝒪) = GL_N(𝒪[F])`;
  - `G(F)^{0+}`, the kernel of reduction `GL_N(𝒪[F]) → GL_N(𝓀[F])`;
  - the index of `G(F)^{0+}` in `G^0(𝒪)`, which is `|GL_N(𝓀[F])|`, that is
    `∏_{i < N} (q ^ N - q ^ i)` with `q = Nat.card 𝓀[F]`.
- For `N = n + 1`, it proves that these two subgroups are the Library's
  concrete matrix subgroups `Conductor.integralSubgroup 𝒪[F] n` and
  `Conductor.principalLevelSubgroup F n 1`. This is a proved comparison
  between the abstract depth-zero layer and the concrete `GL_n` theory.

## Provenance

The module is derived. Its statements are standard facts about `GL_N` over
a discrete valuation ring. Here they are obtained by applying published
Library results to the standard model.

The task objective (Task 3557) asks for this in two places. Its "Regression
examples" section asks for proved examples. Its "Representation layer"
section asks that the Library's concrete `GL_n` results be recovered from the
general theory, with proved comparisons.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Proposition 8.4.14 (printed p. 306 / PDF p. 337), for `G` split over `K`:
  the connected model `G^0_F` of a facet `F` is reductive exactly when `F` is
  a hyperspecial vertex. In that case `G^0_F = G^1_F`, and the maximal
  reductive quotient of the special fibre is the special fibre itself. The
  identity quotient below is this situation: the special fibre is already
  connected reductive, so the radical is trivial.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0}/P_{x,0+}` with the
  `f`-points of the reductive quotient. For `GL_N` at the standard
  hyperspecial vertex this is `GL_N(𝓀[F])`.

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
constructed `GL_N` data. The KP values above are the values these results are
compared against. The order of `GL_N(𝔽_q)` is Mathlib's
`Matrix.card_GL_field`.

## Setting

The general part is stated for a commutative local domain `R` in universe
`u`, a field `K` with `[Algebra R K] [IsFractionRing R K]`, a generic group
`G` over `Spec K` and `D : RelativeComponentModelData R K G`.

The `GL_N` model part is stated for a domain `R` with fraction field `K` and
`N : ℕ`. It uses the Library's group scheme
`GeneralLinear.groupScheme (Fin N) (CommRingCat.of R)` and its standard model
`GeneralLinear.standardIntegralModel R K (Fin N)`. A point `g` over a field is
read as a matrix through `GeneralLinear.rationalPointsEquiv N _ g`, which
lands in `Langlands.GeneralLinear N _ = GL (Fin N) _`.

The local-field part is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
`𝒪[F]` is its valuation ring and `𝓀[F]` its residue field.

The file sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as do the imported
modules `FiniteReductiveQuotient` and `IntegralModel.GeneralLinearLattice`.

## Declarations

### The identity quotient

These are in namespace
`Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData`.

- `identityQuotient D` (definition): the `SpecialFibreQuotientData D` with
  radical the trivial group `Grp.trivial _`, radical inclusion
  `kernelUnit _`, quotient the neutral special fibre itself and projection
  `𝟙 _`. The quotient is affine, as a base change of the affine neutral model.
  A private lemma records this affineness.
- `identityQuotient_isReductiveQuotient`: if
  `IsConnectedReductive D.neutral.specialFibre`, then `identityQuotient D`
  satisfies `IsReductiveQuotient`, in three parts.
  - The unit inclusion is the unipotent radical. This uses the published
    `isUnipotentRadical_kernelUnit` and
    `IsConnectedReductive.hasTrivialUnipotentRadical`.
  - The identity is an fppf quotient by the range of the unit inclusion. It is
    flat, surjective and locally of finite presentation. Its kernel range
    equals the range of `kernelUnit`: both are the trivial subgroup functor,
    by `range_kernelUnit` and `mem_range_kernelι_iff`.
  - The quotient is the given connected reductive special fibre.
- `identityQuotient_radicalPoints`: the radical's residue-field points are
  `⊥`.
- `identityQuotient_positivePoints`: `(identityQuotient D).positivePoints`
  equals the published `D.neutral.congruenceSubgroup`, the image in `G` of
  the kernel of reduction.
- `mem_identityQuotient_positivePoints`: `g` is positive exactly when
  `g = D.neutral.integralPointMap x` for an integral section `x` with
  `D.neutral.reduction x = 1`.

### The standard `GL_N` model

These are in namespace `Langlands.GroupScheme.GeneralLinear`, beside the
published `standardIntegralModel`.

- `glRingEquiv_pointsEquiv_baseChangeSectionHom`: for a ring map
  `φ : A →+* B` and a section `x` of `GL_N` over `Spec A`, consider the base
  change of `x` along `Spec φ`. Read through the base-change point
  correspondence and `pointsEquiv`, with entries moved from `Γ(Spec B)` to
  `B`, it is `Matrix.GeneralLinearGroup.map φ (rationalPointsEquiv N _ x)`.
  The proof uses the published `baseChangePointsEquiv_baseChangeSectionHom`,
  `pointsEquiv_naturality` and `Scheme.ΓSpecIso_naturality`.
- `standardSectionsEquiv R K N` (definition): the integral sections of
  `standardIntegralModel R K (Fin N)` are `GL (Fin N) R`, through the
  published `rationalPointsEquiv N (CommRingCat.of R)`.
- `standardIntegralModel_integralPointMap`, reused from
  [`GeneralLinearStandardPoints`](../../GroupScheme/IntegralModel/GeneralLinearStandardPoints.md):
  the matrix of the image of an
  integral section `x` in the `K`-points is
  `Matrix.GeneralLinearGroup.map (algebraMap R K) (standardSectionsEquiv R K N x)`.
  The proof uses the published `pointsEquiv_comp_baseChangeIso_hom`.
- `mem_standardIntegralModel_integralPoints`: `g` lies in the integral points
  of the standard model exactly when its matrix is
  `Matrix.GeneralLinearGroup.map (algebraMap R K) u` for some
  `u : GL (Fin N) R`.

### The local-field depth-zero data

These are in namespace `Langlands.BruhatTits.IntegralModels`.

- `generalLinearModelData F N` (definition): the
  `RelativeComponentModelData 𝒪[F] F (GeneralLinear.groupScheme (Fin N)
  (CommRingCat.of F))` whose full and neutral models are both
  `GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)`. It is the published
  `IntegralModel.relativeComponentData_of_reductive_localField`. Its inputs
  are the published `isConnectedReductive_generalLinear` over `F` and the
  same fact over `𝓀[F]`, transported to the special fibre by
  `IsConnectedReductive.of_iso` and `GeneralLinear.baseChangeIso`.
- `generalLinearModelData_neutral`: the neutral model is the standard model
  (by `rfl`).
- `isConnectedReductive_generalLinearSpecialFibre`: the special fibre of the
  neutral model is connected reductive.
- `generalLinearQuotientData F N` (definition): `identityQuotient` of
  `generalLinearModelData F N`.
- `generalLinearQuotientData_isReductiveQuotient`: it satisfies
  `IsReductiveQuotient`.
- `generalLinearSpecialFibrePointsEquiv F N` (definition): a group
  isomorphism `rationalPoints (generalLinearModelData F N).neutral.specialFibre
  ≃* GL (Fin N) 𝓀[F]`. It composes the published base-change point
  correspondence along `IntegralModel.residueBaseMap 𝒪[F]`, the published
  `GeneralLinear.pointsEquiv` and the entrywise identification
  `Γ(Spec 𝓀[F]) ≅ 𝓀[F]`.
- `generalLinearSpecialFibrePointsEquiv_reduction`: for an integral section
  `x`, the matrix of its reduction is
  `Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F])
  (GeneralLinear.standardSectionsEquiv 𝒪[F] F N x)`.
- `generalLinear_index_positivePoints_subgroupOf`: the index of `G(F)^{0+}`
  in `G^0(𝒪)`, as `Subgroup.subgroupOf` of
  `(generalLinearQuotientData F N).positivePoints` in
  `(generalLinearModelData F N).neutral.integralPoints`, is
  `Nat.card (GL (Fin N) 𝓀[F])`. The proof applies the published
  `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf` and
  transfers along `generalLinearSpecialFibrePointsEquiv`.
- `generalLinear_index_positivePoints_subgroupOf_eq_prod`: the same index is
  `∏ i : Fin N, (Nat.card 𝓀[F] ^ N - Nat.card 𝓀[F] ^ (i : ℕ))`, by
  Mathlib's `Matrix.card_GL_field`.
- `mem_generalLinear_positivePoints`: `g` lies in
  `(generalLinearQuotientData F N).positivePoints` exactly when there is
  `u : GL (Fin N) 𝒪[F]` with
  `Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) u = 1` and
  `rationalPointsEquiv N _ g = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F]
  F) u`.
- `mem_generalLinear_integralPoints`: `g` lies in
  `(generalLinearModelData F N).neutral.integralPoints` exactly when its
  matrix is `Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F) u` for some
  `u : GL (Fin N) 𝒪[F]`.

### Comparison with the concrete `GL_{n+1}` subgroups

These are also in namespace `Langlands.BruhatTits.IntegralModels`, for
`n : ℕ` and rank `n + 1`. The concrete subgroups are the published
`Langlands.Conductor.integralSubgroup` and
`Langlands.Conductor.principalLevelSubgroup`. They are subgroups of
`GL (Fin (n + 1)) F`, built from the ring `(ValuativeRel.valuation F).integer`,
which is `𝒪[F]`.

- `generalLinear_integralPoints_map_eq_integralSubgroup`: the image of
  `(generalLinearModelData F (n + 1)).neutral.integralPoints` under
  `rationalPointsEquiv (n + 1) _` is `Conductor.integralSubgroup 𝒪[F] n`, the
  range of `GL_{n+1}(𝒪[F]) → GL_{n+1}(F)`.
- `generalLinear_positivePoints_map_eq_principalLevelSubgroup`: the image of
  `(generalLinearQuotientData F (n + 1)).positivePoints` is
  `Conductor.principalLevelSubgroup F n 1`. That is the image of the kernel of
  reduction modulo `𝔪 ^ 1`.
- `generalLinear_principalLevelSubgroup_relIndex`: the relative index
  `(Conductor.principalLevelSubgroup F n 1).relIndex
  (Conductor.integralSubgroup 𝒪[F] n)` is `Nat.card (GL (Fin (n + 1)) 𝓀[F])`.
  The proof transports the index statement above along the matrix
  isomorphism (Mathlib's `Subgroup.relIndex_map_map_of_injective`).

## Scope

No building and no point `x` appear. Nothing here identifies the standard
model with KP's `G^0_x` for the standard hyperspecial vertex, or with a
finite-type Néron model. `G^0(𝒪)` is not identified with KP's `P_{x,0}`, and
`G(F)^{0+}` is not identified with `P_{x,0+}`. The equalities with KP's values
hold only through the explicit descriptions above. Only the standard model on
the coordinate lattice is treated. Other lattices, other vertices,
non-hyperspecial parahorics, `SL_N` and other forms are not covered. The
comparison with the concrete `Conductor` subgroups covers ranks `n + 1 ≥ 1`
and only level one.
