# The translation and the fiber transports in fixed compact charts

Module `Langlands.Representation.Plancherel.ActualConjugateLeviChartConstancy`.

The actual coefficient fibers over the unitary parameters are identified with
one fixed compact carrier by `ActualCommonLeviCompactTensor.compactTensorEquiv`
(restriction to `K × K`). This module shows that the unitary translation and
the canonical fiber transports do not depend on the parameter once they are
read in these charts (`chartValue`). Both kinds of map act on sections by
left translation by a point of `K`, followed by a value map. After the
unramified twists are removed, that value map is a fixed map independent of
the parameter, so `compactValue_const_of_eval` applies.

- `translated_untwist_eval`: if an equivalence of the published fibers is the
  actual product left translation by `g` followed by `coefficientCongr` along
  an inducing equivalence whose vector map is the identity of the carrier of
  `A`, then after removal of the twists it reads the source values at the left
  translate by `(g, g)⁻¹`, through the fixed coefficient-value conjugation
  `TranslatedCoefficientValue.conjugateValue`.
- `unitaryTranslation_chartValue_const`: the unitary translation
  `ActualParabolicUnitaryTranslation.unitaryTranslation` has the same chart
  value at all unitary parameters. This uses `unitaryTranslation_eq` and
  `unitaryTwistEquiv_linear_heq`.
- `anchorChange_untwist_eval` uses a fixed untwisted comparison `cmp` from the
  pullback of `A` along the anchor change to `B`. The transport applies
  `coefficientCongr` along an inducing equivalence with the underlying linear
  map of `cmp.symm` and then applies inverse product left translation by the
  identity. After untwisting, the composite applies
  `productCoefficientLeviEquiv cmp.symm` to the `B` coefficient value at `k`
  and then applies inverse coefficient-value conjugation at the identity.
- `anchorChange_coefficientMap` proves coefficient preservation for this
  type of transport. It applies the inverse translated compact integral
  identity at the identity point of `K`, using admissibility of the twisted
  inducing representations.
- `identityTransport`, `identityTransport_eq`, `identityComparison` and
  `identityTransport_chartValue_const`: the identity-arrow transport
  `ActualConjugateLeviFiberTransport.identityEquiv`, written between the
  displayed fibers, is constant in the charts. The comparison `cmp` is the
  identity vector map from the pullback along conjugation by the identity point
  to `conjugateRepresentation χ 1 A`, which intertwines by `identity_point_eq`.
- `inverseTransport_chartValue_const` applies the same evaluation argument
  to the transport after conjugation by `g` and then by `g⁻¹`. The untwisted
  comparison comes from `inverse_point_eq`, and
  `inverseInducingEquiv_linear_heq` identifies the underlying map of the
  twisted equivalence.
- `multiplicationTransport_chartValue_const` compares conjugation by `t`
  followed by conjugation by `s` with conjugation by `s * t`. The untwisted
  comparison comes from `multiplication_point_eq`, with the underlying map
  identified by `multiplicationInducingEquiv_linear_heq` after twisting.

The translation and comparison formulas are in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*
(2003), V.3, printed p. 295, PDF p. 61.
The left-translation and twist bookkeeping is internal to the Library's
presentation of the actual coefficient fibers.
