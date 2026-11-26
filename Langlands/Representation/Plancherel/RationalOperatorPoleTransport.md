# Pole presentations under a Levi scheme isomorphism

For affine group schemes locally of finite type over a nonarchimedean local field, `rationalUnramifiedParameterHomeomorph` carries a character along a scheme isomorphism by composing with the inverse map on rational points. The inverse character transport follows from `rationalUnramifiedCharacterRestrict_transport` in `DynamicOppositeConjugationScalar`.

`RationalUnitaryPoleFactorization.parameterPullback` maps each integral basis by the valuation-image isomorphism induced by the inverse scheme map. The identity `rationalValuationImageMap_projection` shows that the first coordinate of the transported basis evaluates at the transported point. The root-evaluation formula follows from `rationalUnramifiedBasisLaurentEquiv_eval` and `finiteLaurentCoordinateRoot_eval_cons`. This identifies each root power under pullback. The remainder stays nonzero at unitary characters by `rationalUnitaryUnramifiedCharacterRestrict`.

`RationalOperatorPolePresentation.parameterPullback` pulls back the polynomial numerator by `IsPolynomialOn.parameterPullback` and evaluates the original cross identity at the transported parameter. `RationalOperatorContinuationData.parameterPullback` gives the same transport for the original continuation and retains denominator nonvanishing throughout the preimage of its domain. The source and target coefficient carriers have independent universes.

These are algebraic transport constructions for the character parameters of Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d’après Harish-Chandra*, IV.1 and V.1 (printed pp. 276–277 and 288–289), registered as `waldspurger-2003-plancherel`, SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
