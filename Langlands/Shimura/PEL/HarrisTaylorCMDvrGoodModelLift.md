# Normalized positive polarized actions over a DVR from a good model

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Invariance of the normalized condition

`harrisTaylorCMDeterminantDimensionCondition_of_iso` shows that the normalized joint
condition `D.HarrisTaylorCMDeterminantDimensionCondition C p` passes from `Y` to `X`
along an equivariant rational isomorphism `e : X ≅ Y` of rational algebra actions.
The determinant part uses that the two actions have the same isomorphism class
(`RationalAlgebraAction.classOf_eq_iff`) and the class form of the determinant
condition (`harrisTaylorCMDeterminantClassCondition_classOf`). The dimension part is
the published invariance of relative dimension under rational isomorphism,
`rationalIsoRelativeDimension`.

## Auxiliary data

- `dvrLiftPrerequisites` bundles the named tensor and Picard statements into the
  Library's `PolarizedFiniteLevel.Prerequisites`, with the published theorem
  `dualAbelianBaseChange` and the given polarization base-change statement.
- `constructedDualWitness G` is a dual witness for an abelian scheme over a
  quasi-separated base, obtained from `dualEvaluationDataOfGeometry` applied to the
  published `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`.

## The lift

`dvrNormalizedLift_of_goodModel` takes a discrete valuation ring `V` with fraction
field `K`, the fraction-field morphism `j = Spec.algebraMap V K`, a structure
morphism `β : Spec V ⟶ Spec F`, a positive polarized action `X` over `Spec K` that
satisfies the normalized determinant and numerical conditions for `j ≫ β`, an
abelian scheme `G` over `Spec V`, and an isomorphism `e₀` from the generic fibre of
`G` to the abelian scheme of `X`. It produces a positive polarized action `Y` over
`Spec V` satisfying both conditions for `β`, the unit `1/2` and an equivariant
rational isomorphism `e` from the restriction of `Y` to `X`, with
`PositivePolarizedActionReductionMultiple … j Y X (1/2) e`.

The proof proceeds as follows.

1. `transportDvrGenericPolarizedAction` moves `X` along `e₀` to a positive polarized
   action `X'` on the generic fibre of `G`, with the pulled-back dual witness of
   `constructedDualWitness G`; its polarization is the rational dual pullback of that
   of `X` along `e₀` (`homToHom0_transportDvrGenericPolarization`).
2. `extendDvrPolarizedAction` extends `X'` to `Y` over `Spec V`: its action is the
   unique extension of the action of `X'` (`extendDvrRationalAction`) and its
   polarization is the extension whose restriction is twice that of `X'`
   (`pullbackMap_extendDvrPolarizationDouble`).
3. The isomorphism `e` is the identity of the generic fibre of `G`, which is
   equivariant because the restricted action equals the action of `X'`
   (`rationalBaseChangeEnd_extendDvrRationalAction`), followed by
   `transportDvrGenericActionIso`. Its underlying rational map is `e₀`.
4. For the multiplier, fix any dual data `W'` on the generic fibre. The trivial
   equation for the identity of `G` (`IsRationalDualPullbackMultiple.id`) base
   changes by `IsRationalDualPullbackMultiple.integral_baseChange_of_naturality`
   (using `dualityNaturality`) to an equation with multiplier one between the base
   changes of the polarization of `Y` for `W'` and for the pulled-back witness. The
   transport and doubling formulas give the equation with multiplier `1/2` from the
   latter to the polarization of `X` along `e₀`. Composing
   (`IsRationalDualPullbackMultiple.comp`) and `rationalBaseChangeHom_identity` give
   the required equation for `W'`.
5. For the conditions, `determinantDimensionCondition_iff` turns the conditions on
   `X` into the joint normalized condition. The invariance lemma moves it to `X'`, and
   it holds for the restriction of `Y` because the actions agree. The published DVR
   reflection `harrisTaylorCMDvrNormalization` gives the condition for `Y` over
   `Spec V`, which `determinantDimensionCondition_iff` splits again.

## Provenance

Internal. The module composes the published DVR transport, extension and
normalization results of `HarrisTaylorCMDvrGenericTransport`,
`HarrisTaylorCMDvrPolarizedAction`, `HarrisTaylorCMDvrPolarization` and
`HarrisTaylorCMDvrNormalization` with the Library's coherence of rational dual
pullback. The multiplier `1/2` reflects that the extended polarization restricts to
twice the generic one.
