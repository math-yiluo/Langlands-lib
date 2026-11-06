# Actual CM action schemes for projective families over noetherian affine bases

This internal construction produces the closed Harris CM action scheme for a
supplied projective abelian family over a noetherian affine base. Neither a
relative-endomorphism representative nor a mixed relative-Hom representative is
an input. The construction supplies the scheme, its geometry, its natural
classification of full integral actions, and its actual universal action.

All declarations are in
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel.ProjectiveCMAction`.
The arithmetic carriers and schemes have universe zero.

## Inputs and conditions

Retain the original number fields, scalar towers, central simple unitary datum
`D`, auxiliary imaginary quadratic field, and normalized Harris signature charts
`C`. Supply the prerequisite package `P`, a commutative noetherian ring `R`,
a morphism `p : Spec R ⟶ Spec F`, an actual abelian scheme `B/Spec R`,
and a proof `hB : IsHProjective B.X.hom`. The dual witness `W` and actual
morphism `lam : B ⟶ W.dual P` are also inputs. A polarization condition on
`lam` is not required for this action-scheme construction.

The integral order is the existing `D.harrisHodgePELIntegralOrder C`, with its
original finite integer basis. On a test `T` over `Spec R`, the represented
predicate is exactly `harrisIntegralCMFullActionCondition`: the actual integral
Rosati equations for every element of that order, together with the existing
normalized rational Lie determinant for the canonical rational extension of
the integral action. The family is the direct pullback
`(baseChange T.hom).obj B`. Its dual witness and map are the canonical pullbacks
of the supplied `W` and `lam`. The positive auxiliary involution and conjugated
reflex coefficient map in the original predicates are preserved.

## Constructed scheme and geometry

`ProjectiveIntegralAction.endomorphismScheme R B hB` constructs the actual
relative-endomorphism representative from the supplied projective family.
Its `endomorphismSchemeLocallyNoetherianIso` supplies the natural comparison
on all locally noetherian tests. These are constructions from published
endomorphism representability and affine-extension results, rather than
additional inputs in this module.

`scheme` applies `harrisIntegralCMClosedActionLocus` to that representative
and comparison. Write `Z` for this actual object of `Over (Spec R)`.
`inclusion` is its actual closed inclusion into
`ProjectiveIntegralAction.scheme R B hB basisO`, the finite unit and ordered
basis multiplication equation scheme. `inclusion_isClosedImmersion` reuses
the closed-locus theorem. The instances `scheme_locallyOfFiniteType` and
`scheme_isSeparated` export the existing closed-locus geometry over
`Spec R`. `scheme_isLocallyNoetherian` follows from local finite type over
the noetherian affine base.

`schemeIso` is the existing natural full-action representation with the
constructed endomorphism representative substituted. Its source is
`uliftYoneda.{0}.obj Z` restricted to the full locally noetherian test
category over `Spec R`. Its target is the unchanged
`harrisIntegralCMFullActionSubfunctor`. In particular, its naturality ranges
over every morphism of that full test category.

## Actual universal action and classification

`universalAction` is the integral ring homomorphism on the direct family
`(baseChange Z.hom).obj B` obtained by restricting the actual universal
action of the raw integral-action equation scheme along `inclusion`.
The restriction is the existing `relativeEndRestrict`, with its canonical
comparisons for successive pullbacks.

For every locally noetherian test `T`, `homEquiv` gives an equivalence between
actual morphisms `T ⟶ Z` in `Over (Spec R)` and actual integral actions on
the direct family `B_T` satisfying the full original action condition.
`homEquiv_apply` identifies its value literally:

```text
(homEquiv k).val = (relativeEndRestrict B k).comp universalAction.
```

The proof first applies the published full-action value formula, which
restricts the raw universal action along `k ≫ inclusion`. Ring-homomorphism
extensionality and `Cartier.restrict_comp` identify this with the displayed
restriction of the new universal action.

`universalAction_existsUnique` proves that every actual action satisfying
the full condition has exactly one such classifying morphism, specified by
this literal equality. The morphism is the inverse image under `homEquiv`;
the inverse law gives its value, and injectivity gives uniqueness.
`universalAction_restrict_condition` projects the condition of the
classified action and rewrites by the value formula. Finally,
`universalAction_condition` applies this result to the identity of `Z`,
which is an allowed locally noetherian test, and uses `Cartier.restrict_id`.
Thus the actual universal action itself satisfies all the original equations
and the normalized determinant with the canonical direct pullback dual data.

## Provenance and scope

The provenance is internal composition of the published
`ProjectiveIntegralActionScheme` and `HarrisIntegralCMClosedActionLocus`
constructions, together with the original relative-Hom restriction laws.
No new external source assertion is made. All imported pairs are preserved.

The family, its projectivity, the chosen dual witness, and `lam` remain
supplied. The result does not construct an ambient ordinary polarized
moduli scheme, an integral model of an arbitrary rational action, adelic level
data, or a comparison with the full normalized rational-isogeny presheaf.
Smoothness, division-case projectivity of a final representing scheme, and
output admissibility remain separate obligations of the unchanged
`DivisionCMRepresentabilityStatement`.
