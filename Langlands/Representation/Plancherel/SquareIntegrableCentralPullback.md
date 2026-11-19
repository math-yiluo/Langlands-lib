# Pullback of the square-integrable central data

Use a continuous group isomorphism to transport the central data between the literal inducing Levi in an ambient group and its copy in an intermediate Levi. The construction also covers any groups and continuous group isomorphism with the displayed Borel quotient hypotheses.

The central subgroup is its preimage under the isomorphism. `centralSubgroupPullbackMeasure` is the pushforward of the original Haar measure along the inverse quotient isomorphism, which is Haar and pushes forward back to the original measure. The square-integrability comparison then uses `isSquareIntegrableModCentralSubgroup_comp_iff` for the pulled-back representation on the same coefficient carrier. Finally, the common norm kernel is the inverse image of the original common norm kernel. Mapping the join with the pulled-back central subgroup recovers the original join and hence gives the prescribed finite quotient by quotient equivalence.

These are derived transport facts for the central-quotient hypotheses used in the opposite scalar problem from Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*, 2003, IV.3(6) and V.2.1. The measure transport keeps the given scale.
