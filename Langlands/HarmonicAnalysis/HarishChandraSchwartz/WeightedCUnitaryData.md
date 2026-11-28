# Nonvanishing of the ambient package scalar

`standardLeviDensityCenter` is the image of the original split central subgroup under the inverse of `standardLeviDynamicHomeomorph`. It is the split center in the coordinates of the dynamic Levi used by the ambient density package.

`standardLeviDensityCanonicalScalarNonzero` proves nonvanishing of the opposite-intertwiner scalar entering the density in Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), IV.3 and V.2, pp. 285–287 and 292–294.

The proof uses the compatibility of `standardLeviDynamicHomeomorph` with `standardLeviParameterIso` on rational points to express the transported center as the range of a split component. It pushes the quotient measure forward under the inverse of `quotientContinuousMulEquiv`, so the forward pushforward recovers the original measure. It then uses `isSquareIntegrableModCentralSubgroup_comp_iff` and `isIrreducible_comp_continuousMulEquiv_iff` to apply `DynamicInducedOrbit.DensityPackage.canonicalScalar_ne_zero_of_squareIntegrable`.
