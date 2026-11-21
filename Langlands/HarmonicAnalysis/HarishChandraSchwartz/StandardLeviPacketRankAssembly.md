# Rank induction for source-normalized standard-Levi packets

`StandardLeviPacketProperFaceExpansionAt` supplies the lower density packages at the
literal intersection of a common special compact with the actual output Levi.
It supplies `WeightedWeakExpansionStatement` for those packages and for the
upper package moved to the same compact by `upperDensityAtPacketCompact`.
`StandardLeviPacketProperFaceExpansionStatement` quantifies this input over the
inducing data with the given local field, including the Borel quotient and its
Haar measure. The field and representation carrier have independent universes.

`standardLeviPacketWeakBoundsAt_of_rankIH` chooses a standard cocharacter for
the proper face and uses `exists_representatives_liftsInCompact` to choose Weyl
lifts in the common compact. The two compact equalities give
`SourceCompactNormalization`. The published
`weightedPacketIdentity_of_weightedWeakExpansion` integrates the pointwise
expansion with the original character Haar and its conjugate measures. The
strict-rank specialization in `lowerDynamicPacketChamberEstimates_of_rankIH`
uses the continuity component of the smaller-rank joint theorem. The estimate
`rationalOrbitLevelWeakPacketRapid_of_commonCompact_lowerEstimates` then gives
the weak bound with the original upper weight, matrix height and character Haar.

`standardLeviPlancherelWavePacketAtRank_of_properFaceExpansion` proves
`StandardLeviPacketRankReductionStatement` by strong induction with
`standardLeviPlancherelWavePacketRankZero` as the base case.
Bruhat–Tits availability gives `HasSpecialPacketCompact` through
`hasSpecialPacketCompact_of_availability`. The special-compact synthesis
theorem derives the exact joint conclusion from the proper-face bounds,
using the published constant-term threshold and positive decay results. The
upper package is assembled from the original continuation and regularity
parameters. The original packet compact and continuation compact are separate.

This derived reduction implements the semisimple rank induction of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), VI.3.1, printed pp. 303–305. It has explicit
inputs for the structural availability, lower density packages and pointwise
weighted expansion. The conclusion is the existing joint target at each rank
under these inputs.
