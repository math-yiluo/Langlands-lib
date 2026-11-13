# Depth-zero data for the split torus `G_m` over a local field

This module gives the split-torus regression example for the depth-zero
layer of `Langlands.BruhatTits.IntegralModels`. Earlier modules state
results for supplied `D : RelativeComponentModelData R K G` and
`Q : SpecialFibreQuotientData D`. Here both are constructed for
`G = G_{m,F}` over a nonarchimedean local field `F`, and the quotient is
proved to satisfy `IsReductiveQuotient`. With these constructed data, the
module computes the groups that the general theorems describe:

- `G^0(𝒪) = 𝒪[F]ˣ`;
- `G(F)^{0+} = 1 + 𝔪`, the units of `𝒪[F]` with residue `1`;
- the index of `G(F)^{0+}` in `G^0(𝒪)` is `q - 1`, where `q = Nat.card 𝓀[F]`.

When `q = 2`, the index is `1`. This is the small-residue case.

## Provenance

The module is derived. Its statements are standard facts about `G_m` over a
discrete valuation ring. Here they are obtained by applying published Library
results to the canonical model `G_{m,𝒪[F]}`.

The task objective (Task 3557, section "Regression examples") asks for proved
examples for split tori, including a small-residue-characteristic case where
the theory supports it.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Definition 2.5.13 (printed p. 90 / PDF p. 121) defines the Iwahori subgroup
  `T(k)_0` of a torus as the norm image of the maximal bounded subgroup over a
  splitting extension. For the split torus `G_m`, this subgroup is
  `𝒪ˣ`.
- Equation (13.1.1) (printed p. 467 / PDF p. 498) defines the standard
  filtration `T(k)_r = {t ∈ T(k)_0 | ω(χ(t) - 1) ≥ r for all χ ∈ X^*(T)}` for
  `r > 0`. For `G_m`, the union over `r > 0` is `1 + 𝔪`.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0}/P_{x,0+}` with the
  `f`-points of the reductive quotient. For `G_m` this is `𝓀[F]ˣ`, of order
  `q - 1`.

The authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) do not
amend these three items. In Section 2.5 (PDF p. 24) they amend 2.5(b),
Remark 2.5.11 and Remark 2.5.15. In Chapter 13 (PDF p. 49) they amend
13.5.2, 13.6.2 and 13.8.5. In Appendix B (PDF p. 50) they amend only
Section B.10, not the standard filtration of B.5.

KP's objects are not used in the Lean statements. The module computes the
Library's `D.neutral.integralPoints`, `Q.positivePoints` and the index for
the constructed `G_m` data. The KP values above are the values these results
are compared against.

## Setting

`F` is a field in universe `u` with `ValuativeRel F`, `TopologicalSpace F`
and `IsNonarchimedeanLocalField F`. `𝒪[F]` is its valuation ring and `𝓀[F]`
its residue field. The generic group is `(Gm (Spec (CommRingCat.of F))).toGrp`.
A point `g` of it is read as a unit of `F` through
`Gm.affinePointsEquiv (𝟙 _) g`.

The file sets `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` to `false`, as do the imported
modules `FiniteReductiveQuotient` and `IntegralModel.Multiplicative`.

## Declarations

All declarations are in namespace `Langlands.BruhatTits.IntegralModels`.

- `multiplicativeModelData F` (definition): the
  `RelativeComponentModelData 𝒪[F] F (Gm (Spec (CommRingCat.of F))).toGrp`
  whose full and neutral models are both the published canonical model
  `IntegralModel.multiplicative 𝒪[F] F`. It is the published
  `IntegralModel.relativeComponentData_of_reductive_localField`, applied with
  the published fact `isSplitTorus_gm` that `G_m` is a split torus, over `F`
  and after base change to `𝓀[F]`. That construction supplies smoothness,
  connected fibres and the relative-identity-component property.
- `multiplicativeModelData_neutral`: the neutral model is
  `IntegralModel.multiplicative 𝒪[F] F` (by `rfl`).
- `isSplitTorus_multiplicativeSpecialFibre`: the special fibre of the neutral
  model is a split torus (`IsSplitTorus.baseChange` of `isSplitTorus_gm`).
- `multiplicativeQuotientData F` (definition): the
  `SpecialFibreQuotientData (multiplicativeModelData F)` with radical the
  trivial group `Grp.trivial _`, radical inclusion `kernelUnit _`, quotient
  the special fibre itself and projection `𝟙 _`. The quotient is affine
  because a split torus is affine over its base.
- `multiplicativeQuotientData_isReductiveQuotient`: this data satisfies
  `IsReductiveQuotient`, in three parts.
  - The unit inclusion is the unipotent radical, by the published
    `isUnipotentRadical_kernelUnit` and the fact that a split torus has
    trivial unipotent radical.
  - The identity is an fppf quotient by the range of the unit inclusion. It is
    flat, surjective and locally of finite presentation. Its kernel range
    equals the range of `kernelUnit`: both are the trivial subgroup functor,
    by `range_kernelUnit` and `mem_range_kernelι_iff`.
  - The quotient is connected reductive, since it is a split torus.
- `multiplicativeSpecialFibrePointsEquiv F` (definition): a group isomorphism
  `rationalPoints (multiplicativeModelData F).neutral.specialFibre ≃* 𝓀[F]ˣ`.
  It composes the published `Gm.baseChangeUnitsEquiv` along
  `IntegralModel.residueBaseMap 𝒪[F]` with the units of
  `Γ(Spec 𝓀[F]) ≅ 𝓀[F]`.
- `multiplicative_index_positivePoints_subgroupOf`: the index of
  `G(F)^{0+}` in `G^0(𝒪)`, as `Subgroup.subgroupOf` of
  `(multiplicativeQuotientData F).positivePoints` in
  `(multiplicativeModelData F).neutral.integralPoints`, is
  `Nat.card 𝓀[F] - 1`. The proof applies the published
  `SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf` (the
  index is the number of `𝓀[F]`-points of the quotient). It then transfers
  along `multiplicativeSpecialFibrePointsEquiv` and uses Mathlib's
  `Nat.card_units`.
- `multiplicative_index_positivePoints_subgroupOf_eq_one`: if
  `Nat.card 𝓀[F] = 2`, the same index is `1`, so `G(F)^{0+} = G^0(𝒪)`.
- `multiplicativeSpecialFibrePointsEquiv_reduction`: for an integral section
  `x`, `multiplicativeSpecialFibrePointsEquiv` of its reduction equals the
  residue map on units applied to `IntegralModel.multiplicativeSectionsEquiv
  𝒪[F] F x : 𝒪[F]ˣ`.
- `multiplicativeQuotientData_radicalPoints`: the radical's residue-field
  points are `⊥`.
- `mem_multiplicative_positivePoints`: a point `g` of `G_{m,F}` lies in
  `(multiplicativeQuotientData F).positivePoints` exactly when there is
  `u : 𝒪[F]ˣ` with `IsLocalRing.residue 𝒪[F] u = 1` and
  `Gm.affinePointsEquiv (𝟙 _) g = Units.map (algebraMap 𝒪[F] F) u`.
- `mem_multiplicative_integralPoints`: `g` lies in
  `(multiplicativeModelData F).neutral.integralPoints` exactly when there is
  `u : 𝒪[F]ˣ` with `Gm.affinePointsEquiv (𝟙 _) g = Units.map (algebraMap 𝒪[F]
  F) u`.

Both membership proofs use the published `IntegralModel.multiplicativeSectionsEquiv`
(integral sections are `𝒪[F]ˣ`) and `IntegralModel.multiplicative_integralPointMap`
(the generic identification sends a section to the same unit in `Fˣ`).

## Scope

No building and no point `x` appear. Nothing here identifies the constructed
model with the finite-type Néron model or with a Bruhat–Tits parahoric group
scheme. `G^0(𝒪)` is not identified with KP's `P_{x,0}`, and `G(F)^{0+}` is not
identified with `P_{x,0+}`. The equalities with KP's values hold only by the
explicit descriptions above. Only the split torus `G_m` is treated, not
general split tori or non-split tori. The small-residue statement takes
`Nat.card 𝓀[F] = 2` as a hypothesis; no particular field such as `ℚ₂` is
constructed.
