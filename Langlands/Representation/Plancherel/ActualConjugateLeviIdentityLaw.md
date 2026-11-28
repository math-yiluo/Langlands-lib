# The identity law for the actual translated comparison

Module `Langlands.Representation.Plancherel.ActualConjugateLeviIdentityLaw`.

- `coefficientMap_injective_dense`: for a normalization `d` with actual split
  center, the published coefficient map `coefficientMap χ hG A d K hK P z` is
  injective for a dense set of unitary parameters `z`. This is
  `ActualCommonLeviCoherence.dense_injective_of_denseUnitaryIrreducibility`
  applied to `ActualCommonLeviV3.denseUnitaryIrreducibility`.
- `identityTargetAt` and `identityReturn`: the identity-arrow target
  presentation and the identity-arrow transport
  `ActualConjugateLeviFiberTransport.identityEquiv`, written over the anchor
  conjugated by the identity point of the compact subgroup `K`, as in the
  statement of `IdentityLaw`.
- `identityReturn_chartValue_const` and `identityReturn_coefficientMap`: this
  transport has a parameter-independent value in the fixed compact charts, and
  it preserves the published coefficient maps. Both are
  `identityTransport_chartValue_const` and `anchorChange_coefficientMap`
  restated.
- `identity_loop`: let `U` be a continuation from the conjugate presentation to
  the identity-arrow target whose compact-chart value is locally finite, and
  such that `U` after the unitary translation preserves the coefficient maps.
  Then the identity-arrow transport undoes `U` after the unitary translation.
  The proof applies `eq_self_of_loop`. The unitary translation and the
  transport are constant in the charts, and `U` is locally finite after the
  continuous map `unitaryConjugateParameter χ 1`. So the composite is weakly
  continuous in the charts and preserves coefficients, which are injective on
  a dense set of parameters. Hence it is the identity.
- `identityLaw`: `IdentityLaw` holds. For an actual comparison `T` at the
  identity point, `IsActualComparison` presents `T` as `ofCommonLevi` of an
  actual normalized comparison `U`. Its regular unitary extension makes the
  compact-chart value of `U` locally finite
  (`isLocallyFinite_of_regularUnitaryExtension`), and the coefficient identity
  of `T` gives the coefficient hypothesis of `identity_loop`.
  `TransportedValue` is then witnessed by the value of `U` after the unitary
  translation.

The identity equation is part of the coherence of the comparisons in
Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.3 formula (1) and Lemma V.3.2,
printed p. 295, PDF p. 61.
