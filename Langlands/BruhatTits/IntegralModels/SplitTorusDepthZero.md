# Depth-zero data for split tori over a local field

This module gives the general split-torus regression example for the
depth-zero layer of `Langlands.BruhatTits.IntegralModels`. Earlier modules
state results for supplied `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D`. Here both are constructed for the split
torus `G = G_m^I` over a nonarchimedean local field `F`, for any finite index
type `I`, and the quotient is proved to satisfy `IsReductiveQuotient`. With
these constructed data, the module computes the groups that the general
theorems describe:

- `G^0(𝒪) = (𝒪[F]ˣ)^I`;
- `G(F)^{0+} = (1 + 𝔪)^I`, the families of units of `𝒪[F]` whose residues
  are all `1`;
- the index of `G(F)^{0+}` in `G^0(𝒪)` is `(q - 1) ^ |I|`, where
  `q = Nat.card 𝓀[F]` and `|I| = Nat.card I`.

When `q = 2`, the index is `1`. This is the small-residue case.

To do this, the module first constructs the canonical model of a split torus
over an integral domain. The Library had no such model: it had a canonical
model of `G_m` (`IntegralModel.multiplicative`) but none of `G_m^I`.

## Provenance

The module is derived. Its statements are standard facts about split tori
over a discrete valuation ring. Here they are obtained by applying published
Library results to the canonical model `G_{m,𝒪[F]}^I`.

The task objective (Task 3557, section "Regression examples") asks for proved
examples for split tori, including a small-residue-characteristic case where
the theory supports it. The rank-one case is the separate module
`Langlands.BruhatTits.IntegralModels.MultiplicativeDepthZero`, stated for
`(Gm (Spec F)).toGrp`. This module does not import it and states no
comparison with it.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Definition 2.5.13 (printed p. 90 / PDF p. 121) defines the Iwahori subgroup
  `T(k)_0` of a torus as the norm image of the maximal bounded subgroup over a
  splitting extension. For the split torus `G_m^I`, this subgroup is
  `(𝒪ˣ)^I`.
- Equation (13.1.1) (printed p. 467 / PDF p. 498) defines the standard
  filtration `T(k)_r = {t ∈ T(k)_0 | ω(χ(t) - 1) ≥ r for all χ ∈ X^*(T)}` for
  `r > 0`. For `G_m^I`, the coordinate characters generate `X^*(T)`, and the
  union over `r > 0` is `(1 + 𝔪)^I`.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0}/P_{x,0+}` with the
  `f`-points of the reductive quotient. For `G_m^I` this is `(𝓀[F]ˣ)^I`, of
  order `(q - 1) ^ |I|`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend these three items. In Section 2.5 (PDF p. 24) they amend 2.5(b),
Remark 2.5.11 and Remark 2.5.15. In Chapter 13 (PDF p. 49) they amend
13.5.2, 13.6.2 and 13.8.5. In Appendix B (PDF p. 50) they amend only
Section B.10, not the standard filtration of B.5.

KP's objects are not used in the Lean statements. The module computes the
Library's `D.neutral.integralPoints`, `Q.positivePoints` and the index for
the constructed split-torus data. The KP values above are the values these
results are compared against.

## Setting

`IntegralModel.splitTorusModel R K I` is stated for a commutative domain `R`
in universe `u`, a field `K` with `[Algebra R K] [IsFractionRing R K]`, and a
type `I : Type u` with `[Finite I]`. The split torus `splitTorus S I` is the
Library's categorical product of `I` copies of `(Gm S).toGrp`.

The local-field part is stated for a field `F` in universe `u` with
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
`𝒪[F]` is its valuation ring and `𝓀[F]` its residue field. The generic group
is `splitTorus (Spec (CommRingCat.of F)) I`. A point `g` of it is read as a
family of units of `F` through `splitTorus.affinePointsEquiv I (𝟙 _) g`.

The file sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as does the imported
module `FiniteReductiveQuotient`.

## Declarations

### The canonical split-torus model

These are in namespace `Langlands.GroupScheme.IntegralModel`, beside the
published `IntegralModel.multiplicative`.

- `splitTorusModel R K I` (definition): the
  `IntegralModel R K (splitTorus (Spec (CommRingCat.of K)) I)` whose group is
  `splitTorus (Spec (CommRingCat.of R)) I`. Its generic identification is the
  published `splitTorus.baseChangeIso (Spec.algebraMap R K) I`. It is affine
  by the published `isAffineHom_splitTorus`. It is flat and of finite type
  because the published `smooth_splitTorus` makes it smooth.
- `splitTorusModel_isSmooth`: this model is smooth over `R`
  (`IntegralModel.IsSmooth`).
- `splitTorusSectionsEquiv R K I` (definition): a group isomorphism from the
  integral sections of the model to `I → Rˣ`, the published
  `splitTorus.affinePointsEquiv I (𝟙 _)`.
- `splitTorusModel_integralPointMap`: for an integral section `x`,
  `splitTorus.affinePointsEquiv I (𝟙 _)` of its image in the `K`-points is
  `fun j => Units.map (algebraMap R K) (splitTorusSectionsEquiv R K I x j)`.
  The proof uses the published `IntegralModel.pointsEquiv_baseChangeSectionHom`
  and the naturality `Scheme.ΓSpecIso_naturality`.

### The local-field depth-zero data

These are in namespace `Langlands.BruhatTits.IntegralModels`.

- `splitTorusModelData F I` (definition): the
  `RelativeComponentModelData 𝒪[F] F (splitTorus (Spec (CommRingCat.of F)) I)`
  whose full and neutral models are both `IntegralModel.splitTorusModel 𝒪[F] F
  I`. It is the published
  `IntegralModel.relativeComponentData_of_reductive_localField`, applied with
  the published fact `isSplitTorus_splitTorus I`, over `F` and after base
  change to `𝓀[F]`. That construction supplies smoothness, connected fibres
  and the relative-identity-component property.
- `splitTorusModelData_neutral`: the neutral model is
  `IntegralModel.splitTorusModel 𝒪[F] F I` (by `rfl`).
- `isSplitTorus_splitTorusSpecialFibre`: the special fibre of the neutral
  model is a split torus (`IsSplitTorus.baseChange`).
- `splitTorusQuotientData F I` (definition): the
  `SpecialFibreQuotientData (splitTorusModelData F I)` with radical the
  trivial group `Grp.trivial _`, radical inclusion `kernelUnit _`, quotient
  the special fibre itself and projection `𝟙 _`. The quotient is affine
  because a split torus is affine over its base.
- `splitTorusQuotientData_isReductiveQuotient`: this data satisfies
  `IsReductiveQuotient`, in three parts.
  - The unit inclusion is the unipotent radical, by the published
    `isUnipotentRadical_kernelUnit` and the fact that a split torus has
    trivial unipotent radical.
  - The identity is an fppf quotient by the range of the unit inclusion. It is
    flat, surjective and locally of finite presentation. Its kernel range
    equals the range of `kernelUnit`: both are the trivial subgroup functor,
    by `range_kernelUnit` and `mem_range_kernelι_iff`.
  - The quotient is connected reductive, since it is a split torus.
- `splitTorusSpecialFibrePointsEquiv F I` (definition): a group isomorphism
  `rationalPoints (splitTorusModelData F I).neutral.specialFibre ≃*
  (I → 𝓀[F]ˣ)`. It composes the published `splitTorus.baseChangePointsEquiv`
  along `IntegralModel.residueBaseMap 𝒪[F]` with, in each coordinate, the
  units of `Γ(Spec 𝓀[F]) ≅ 𝓀[F]`.
- `splitTorus_index_positivePoints_subgroupOf`: the index of `G(F)^{0+}` in
  `G^0(𝒪)`, as `Subgroup.subgroupOf` of
  `(splitTorusQuotientData F I).positivePoints` in
  `(splitTorusModelData F I).neutral.integralPoints`, is
  `(Nat.card 𝓀[F] - 1) ^ Nat.card I`. The proof applies the published
  `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf` (the
  index is the number of `𝓀[F]`-points of the quotient). It then transfers
  along `splitTorusSpecialFibrePointsEquiv` and uses Mathlib's `Nat.card_fun`
  and `Nat.card_units`.
- `splitTorus_index_positivePoints_subgroupOf_eq_one`: if
  `Nat.card 𝓀[F] = 2`, the same index is `1`, so `G(F)^{0+} = G^0(𝒪)`.
- `splitTorusSpecialFibrePointsEquiv_reduction`: for an integral section `x`,
  `splitTorusSpecialFibrePointsEquiv` of its reduction is the family
  `fun j => Units.map (IsLocalRing.residue 𝒪[F])
  (IntegralModel.splitTorusSectionsEquiv 𝒪[F] F I x j)`. The proof uses the
  published `baseChangePointsEquiv_baseChangeSectionHom` and
  `splitTorus.pointsEquiv_naturality`.
- `splitTorusQuotientData_radicalPoints`: the radical's residue-field points
  are `⊥`.
- `mem_splitTorus_positivePoints`: a point `g` of the split torus over `F`
  lies in `(splitTorusQuotientData F I).positivePoints` exactly when there is
  `u : I → 𝒪[F]ˣ` with `IsLocalRing.residue 𝒪[F] (u j) = 1` for every `j` and
  `splitTorus.affinePointsEquiv I (𝟙 _) g = fun j => Units.map (algebraMap
  𝒪[F] F) (u j)`.
- `mem_splitTorus_integralPoints`: `g` lies in
  `(splitTorusModelData F I).neutral.integralPoints` exactly when there is
  `u : I → 𝒪[F]ˣ` with `splitTorus.affinePointsEquiv I (𝟙 _) g =
  fun j => Units.map (algebraMap 𝒪[F] F) (u j)`.

Both membership proofs use `splitTorusSectionsEquiv` (integral sections are
`I → 𝒪[F]ˣ`) and `splitTorusModel_integralPointMap` (the generic
identification sends a section to the same family of units in `Fˣ`).

## Scope

No building and no point `x` appear. Nothing here identifies the constructed
model with the finite-type Néron model or with a Bruhat–Tits parahoric group
scheme. `G^0(𝒪)` is not identified with KP's `P_{x,0}`, and `G(F)^{0+}` is not
identified with `P_{x,0+}`. The equalities with KP's values hold only by the
explicit descriptions above. Only the standard split torus `splitTorus _ I`
is treated. A group merely isomorphic to it, a non-split torus, or a torus
that splits only over an extension is not covered. The small-residue
statement takes `Nat.card 𝓀[F] = 2` as a hypothesis; no particular field such
as `ℚ₂` is constructed.
