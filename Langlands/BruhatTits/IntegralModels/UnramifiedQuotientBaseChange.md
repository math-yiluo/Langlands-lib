# The reductive quotient after maximal-unramified base change

Module `Langlands.BruhatTits.IntegralModels.UnramifiedQuotientBaseChange`.

## Setting

Let `F` be a nonarchimedean local field, in arbitrary universe `u` and either
characteristic. Write `K = inertiaFixedField F` and `O = fixedFieldIntegers F`.
The integer algebra `𝒪[F] → O` and its scalar tower are the local instances of
the Library's `IntegralModel.baseChangeUnramified`. The residue algebra
`𝓀[F] → O/𝔪` is `residueToFixedField F`, as in the published
`UnramifiedReductionPoints`. `D` is relative-component model data of a group
`G` over `𝒪[F]`, and `Q : SpecialFibreQuotientData D` is special-fibre
quotient data.

## Declarations

- `unramifiedResidueSquare M` is the published coefficient-square comparison
  `Descent.squareComparison` for the two residue towers of `𝒪[F] → O`. It
  identifies the special fibre of the base change of `M` to `O` with the
  base change of the special fibre of `M` along `𝓀[F] → O/𝔪`.
- `unramifiedQuotientResidue_isAlgebraic` and
  `unramifiedQuotientResidue_isSeparable`: this residue extension is algebraic
  (`fixedFieldResidueIsAlgClosure F`), and it is separable because `𝓀[F]` is
  finite, hence perfect.
- `SpecialFibreQuotientData.unramifiedBaseChange Q` is quotient data for
  `D.baseChange O K`. Its radical and quotient are the base changes of those of
  `Q` along `𝓀[F] → O/𝔪`. Its radical inclusion is the base change of
  `Q.radicalInclusion` followed by the inverse square comparison. Its
  projection is exactly the published
  `D.neutral.unramifiedSpecialFibreMap Q.projection`.
- `unramifiedBaseChange_projection` unfolds that projection to the square
  comparison followed by the base change of `Q.projection`, by
  `Descent.squareComparisonMap_def`.
- `isReductiveQuotient_unramifiedBaseChange`. If `Q.IsReductiveQuotient`, then
  `(Q.unramifiedBaseChange).IsReductiveQuotient`.
- `mem_positivePoints_iff_unramifiedBaseChange`. If `Q.IsReductiveQuotient`,
  then for every rational point `g` of `G`, `g ∈ Q.positivePoints` holds
  exactly when `rationalExtend F K G g ∈ (Q.unramifiedBaseChange).positivePoints`.

## Proofs

`isReductiveQuotient_unramifiedBaseChange` follows the published proof of
`SpecialFibreQuotientData.isReductiveQuotient_baseChange`
(`UnramifiedFacetSignDescent`), with the residue-tower comparison in place of
`specialFibreSquareIso`.

- The neutral special fibre is smooth, affine and connected
  (`hasConnectedSpecialFibre_of_hasConnectedFibres`).
- The radical clause applies the published `separableAlgebraicUnipotentRadical`
  (CGP Proposition 1.1.9(1)) to the separable algebraic extension
  `𝓀[F] → O/𝔪`, then `IsUnipotentRadical.comp_iso`.
- The fppf clause is `IsFppfQuotient.baseChange` followed by `comapIso` along
  the inverse comparison, with `SubgroupFunctor.range_comp_iso` and
  `range_baseChangeHom`.
- The reductive clause is `IsConnectedReductive.baseChange_of_algebraicExtension`.

`mem_positivePoints_iff_unramifiedBaseChange` rewrites the left side by the
published `positivePoints_eq_comap_unramifiedKernelPoints`
(`SpecialFibrePositiveDescent`). It rewrites the right side by
`positivePoints_eq_specialFibreKernelPoints`, using the fppf clause just
proved. The projection of `Q.unramifiedBaseChange` is literally
`unramifiedSpecialFibreMap Q.projection`, so the two kernel-point subgroups
coincide by definition.

The projection is defined through the Library's irreducible
`unramifiedSpecialFibreMap` rather than through `specialFibreSquareIso`. This
keeps the descent of positive points a definitional consequence of the
published kernel-point descent.

## Provenance

This is internal derived content, composed from the named Library results. It
supplies the base-change compatibility of the maximal reductive quotient of the
special fibre (KP Proposition 9.4.28 and its proof; Kaletha and Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`). No new literature assertion is
made.
